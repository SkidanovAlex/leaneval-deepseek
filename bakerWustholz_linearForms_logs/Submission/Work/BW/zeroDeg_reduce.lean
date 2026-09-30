import Mathlib
import Submission.Work.BW.DefsMP

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity_prop partial-degeneracy reduction; MULT_PROP_CHECK.md below). Your node is `zeroDeg_reduce`. Definitions: Submission.Work.BW.DefsMP (liftIdx, extM; imports DefsB). Import siblings; do not reprove them.

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

/-! ### Auxiliary lemmas for `zeroDeg_reduce` -/

/-- `liftIdx σ` sends `0` to `0`. -/
lemma zeroDeg_liftIdx_zero {N' r : ℕ} (σ : Fin N' → Fin r) : liftIdx σ 0 = 0 := rfl

/-- `liftIdx σ` sends `j.succ` to `(σ j).succ`. -/
lemma zeroDeg_liftIdx_succ {N' r : ℕ} (σ : Fin N' → Fin r) (j : Fin N') :
    liftIdx σ j.succ = (σ j).succ := rfl

/-- `liftIdx σ` is injective whenever `σ` is. -/
lemma zeroDeg_liftIdx_injective {N' r : ℕ} {σ : Fin N' → Fin r} (hσ : Function.Injective σ) :
    Function.Injective (liftIdx σ) := by
  intro a b h
  rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨k, rfl⟩
    · rfl
    · simp only [liftIdx, Fin.cases_zero, Fin.cases_succ] at h
      exact absurd h.symm (Fin.succ_ne_zero (σ k))
  · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨k, rfl⟩
    · simp only [liftIdx, Fin.cases_zero, Fin.cases_succ] at h
      exact absurd h (Fin.succ_ne_zero (σ j))
    · simp only [liftIdx, Fin.cases_succ, Fin.succ_inj] at h
      rw [hσ h]

/-- Reindex a sum from `Fin r` to `Fin N'` along an injective `σ`, when the summand vanishes
off the range of `σ`. -/
lemma zeroDeg_sum_range_eq {A : Type*} [AddCommMonoid A] {N' r : ℕ} (σ : Fin N' → Fin r)
    (hσ : Function.Injective σ) (G : Fin r → A) (hG : ∀ i, i ∉ Set.range σ → G i = 0) :
    ∑ i : Fin r, G i = ∑ j : Fin N', G (σ j) := by
  have h1 : (Finset.univ.filter (fun i : Fin r => i ∈ Set.range σ)).sum G =
      (Finset.univ : Finset (Fin r)).sum G := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hG i hi
  have h2 : (Finset.univ.filter (fun i : Fin r => i ∈ Set.range σ)) =
      (Finset.univ : Finset (Fin N')).map ⟨σ, hσ⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩; exact ⟨j, rfl⟩
  rw [← h1, h2, Finset.sum_map, Function.Embedding.coeFn_mk]

/-- `derC` commutes with the renaming `liftIdx σ`: the terms of `derC` indexed by coordinates
outside `range σ` vanish, and the remaining ones are the derivatives of the renamed polynomial. -/
lemma zeroDeg_derC_rename_liftIdx {N' r : ℕ} (σ : Fin N' → Fin r)
    (hσ : Function.Injective σ) (v : Fin (r+1) → ℂ) (Q' : MvPolynomial (Fin (N'+1)) ℂ) :
    MvPolynomial.rename (liftIdx σ) (derC (v ∘ liftIdx σ) Q') =
      derC v (MvPolynomial.rename (liftIdx σ) Q') := by
  have hφ : Function.Injective (liftIdx σ) := zeroDeg_liftIdx_injective hσ
  have hvars : ((MvPolynomial.rename (liftIdx σ) Q').vars : Set (Fin (r+1))) ⊆
      Set.range (liftIdx σ) := by
    intro a ha
    have h2 := MvPolynomial.vars_rename (liftIdx σ) Q' ha
    rw [Finset.mem_image] at h2
    obtain ⟨b, _, hb⟩ := h2
    exact ⟨b, hb⟩
  have hG : ∀ i : Fin r, i ∉ Set.range σ →
      MvPolynomial.C (v i.succ) * MvPolynomial.X i.succ *
        MvPolynomial.pderiv i.succ (MvPolynomial.rename (liftIdx σ) Q') = 0 := by
    intro i hi
    have hmem : i.succ ∉ (MvPolynomial.rename (liftIdx σ) Q').vars := by
      intro hc
      obtain ⟨b, hb⟩ := hvars hc
      rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨j, rfl⟩
      · rw [zeroDeg_liftIdx_zero] at hb
        exact absurd hb.symm (Fin.succ_ne_zero i)
      · rw [zeroDeg_liftIdx_succ] at hb
        exact hi ⟨j, Fin.succ_inj.mp hb⟩
    simp [MvPolynomial.pderiv_eq_zero_of_notMem_vars hmem]
  have hpd : ∀ a : Fin (N'+1), MvPolynomial.rename (liftIdx σ) (MvPolynomial.pderiv a Q') =
      MvPolynomial.pderiv (liftIdx σ a) (MvPolynomial.rename (liftIdx σ) Q') :=
    fun a => (MvPolynomial.pderiv_rename hφ a Q').symm
  simp only [derC, map_add, map_mul, map_sum, MvPolynomial.rename_C, MvPolynomial.rename_X,
    Function.comp_apply, hpd, zeroDeg_liftIdx_zero, zeroDeg_liftIdx_succ]
  rw [zeroDeg_sum_range_eq σ hσ _ hG]

/-- Iterated version of `zeroDeg_derC_rename_liftIdx`. -/
lemma zeroDeg_iterate_derC_rename_liftIdx {N' r : ℕ} (σ : Fin N' → Fin r)
    (hσ : Function.Injective σ) (v : Fin (r+1) → ℂ) (n : ℕ)
    (Q' : MvPolynomial (Fin (N'+1)) ℂ) :
    MvPolynomial.rename (liftIdx σ) ((derC (v ∘ liftIdx σ))^[n] Q') =
      (derC v)^[n] (MvPolynomial.rename (liftIdx σ) Q') := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      zeroDeg_derC_rename_liftIdx σ hσ, ih]

/-- `applyW` commutes with the renaming `liftIdx σ` (stated for an arbitrary list of steps). -/
lemma zeroDeg_foldr_rename_applyW {N' r q : ℕ} (σ : Fin N' → Fin r)
    (hσ : Function.Injective σ) (w : Fin q → Fin (r+1) → ℂ) (t : Fin q → ℕ)
    (l : List (Fin q)) (Q' : MvPolynomial (Fin (N'+1)) ℂ) :
    MvPolynomial.rename (liftIdx σ)
        (l.foldr (fun m Q' => (derC ((w m) ∘ liftIdx σ))^[t m] Q') Q') =
      l.foldr (fun m Q => (derC (w m))^[t m] Q) (MvPolynomial.rename (liftIdx σ) Q') := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons, ih,
      zeroDeg_iterate_derC_rename_liftIdx σ hσ (w a) (t a)]

/-- Partial degeneracy, step 1 (renaming). If `P` has degree `0` in every torus variable outside
`range σ`, it is the rename of a polynomial `P'` in `N' + 1` variables, with the same partial
degrees, and every derivative evaluation transfers: the derivations `derC v` lose only
the terms `C(vᵢ) Yᵢ ∂ᵢ` with `∂ᵢ P = 0`, and `ptTheta θ s ∘ liftIdx σ = ptTheta (θ ∘ σ) s`. Proof:
`MvPolynomial.exists_rename_eq_of_vars_subset_range`, `MvPolynomial.eval_rename`,
`pderiv_rename`, induction along `List.finRange`. Size 0.6–1.2k. -/
theorem zeroDeg_reduce {r N' q : ℕ} (σ : Fin N' → Fin r) (hσ : StrictMono σ)
    (P : MvPolynomial (Fin (r + 1)) ℂ)
    (hZ : ∀ i : Fin r, i ∉ Set.range σ → P.degreeOf i.succ = 0) :
    ∃ P' : MvPolynomial (Fin (N' + 1)) ℂ, MvPolynomial.rename (liftIdx σ) P' = P ∧
      (∀ i, P'.degreeOf i = P.degreeOf (liftIdx σ i)) ∧
      ∀ (w : Fin q → Fin (r + 1) → ℂ) (t : Fin q → ℕ) (θ : Fin r → ℂ) (s : ℕ),
        MvPolynomial.eval (ptTheta θ s) (applyW w t P) =
          MvPolynomial.eval (ptTheta (θ ∘ σ) s) (applyW (fun k => w k ∘ liftIdx σ) t P') := by
  have hσi : Function.Injective σ := hσ.injective
  have hφ : Function.Injective (liftIdx σ) := zeroDeg_liftIdx_injective hσi
  have hsub : ↑P.vars ⊆ Set.range (liftIdx σ) := by
    intro a ha
    have ha' : P.degreeOf a ≠ 0 := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mp ha
    rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨i, rfl⟩
    · exact ⟨0, zeroDeg_liftIdx_zero σ⟩
    · have hi : i ∈ Set.range σ := by
        by_contra hc
        exact ha' (hZ i hc)
      obtain ⟨j, hj⟩ := hi
      exact ⟨j.succ, by rw [zeroDeg_liftIdx_succ, hj]⟩
  obtain ⟨P', hP'⟩ :=
    MvPolynomial.exists_rename_eq_of_vars_subset_range P (liftIdx σ) hφ hsub
  refine ⟨P', hP', ?_, ?_⟩
  · intro i
    rw [← hP', MvPolynomial.degreeOf_rename_of_injective hφ i]
  · intro w t θ s
    have key := zeroDeg_foldr_rename_applyW σ hσi w t (List.finRange q) P'
    simp only [applyW]
    rw [← hP', ← key, MvPolynomial.eval_rename]
    have hpt : (ptTheta θ s) ∘ (liftIdx σ) = ptTheta (θ ∘ σ) s := by
      funext a
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨j, rfl⟩ <;>
        simp [ptTheta, liftIdx, Fin.cases_zero, Fin.cases_succ, Function.comp_apply]
    rw [hpt]

end Work.BW

import Mathlib
import Submission.Work.BW.DefsMP
import Submission.Work.BW.DefsMult
import Submission.Work.BW.multiplicity_engine
import Submission.Work.BW.quotient_reduction
import Submission.Work.BW.ellW_dichotomy
import Submission.Work.BW.ellW_B_mem_span
import Submission.Work.BW.one_le_ellW_false
import Submission.Work.BW.mem_span_extM
import Submission.Work.BW.extM_sum_abs
import Submission.Work.BW.reduced_orth_mem_span

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD 09-29 20:15: multiplicity_prop DEGENERATE branch design (DESIGN.md below). The branch is TRUE as stated. Case (i) (B≠0 on Deg) is B_eq_zero_of_deg_lt_one, already PROVED. Case (ii) (B=0 on Deg) is the quotient route at level N′, with NO induction: ellW depends only on span_ℂ(range w), and the restricted family has the same span as (e₀,(0,c′)) for a ℚ-basis c′ of (B∘σ)^⊥; ze_engine runs unchanged at level N′<r. Lemmas 1-4 are dispatched top-level: quotient_reduction_core, reduced_span_eq, reduced_ellW_facts (do NOT skip N′=1), mp_pullback. mp_degenerate and the final proof go into multiplicity_prop.lean (owner H21); both are already elaborated in DESIGN.md.

# multiplicity_prop: the degenerate branch (design, 2026-09-29)

Workspace: 3.144 `~/src/curric/fundmath3-runs/bakerWustholz_linearForms_logs`, namespace `Work.BW`.
Notation: `Deg = {k : Fin r | 𝒟 k.succ < 1}` are the degenerate torus coordinates. (H21's notes
call this `Z`. Careful: inside `quotient_reduction.lean` the Finset named `Z` is the complement,
the kept coordinates `{k | 1 ≤ 𝒟 k.succ}`.) `σ : Fin N' → Fin r` enumerates the kept coordinates
in increasing order, and `B' = B ∘ σ`, `ℓ' = ℓ ∘ σ`.

## 1. Rulings

**The degenerate branch is TRUE as stated.** There is no counterexample, and the statement of
`multiplicity_prop` does not need to change, so `group_reduction` is unaffected. The branch splits
by whether `B` vanishes on `Deg`:

* **(i) `B k ≠ 0` for some `k ∈ Deg`: the hypotheses are contradictory.** This is route B1, and
  it holds for every `r` and every `|Deg|`. **It is already proved:** see
  `B_eq_zero_of_deg_lt_one` below.
* **(ii) `B` vanishes on `Deg`: the quotient route works for every `|Deg| ≥ 1`.** This is route B2,
  repaired. H21's worry about `dim span w < N'+1` comes from a false premise. H21 wanted to feed
  the family `c ∘ σ` (`r − 1` vectors, dependent once `|Deg| ≥ 2`) to `ellW_dichotomy`. But `ellW`
  depends **only on `span_ℂ (range w)`**: this is definitional (`ellW := finrank span −
  finrank (span ⊓ lieSub)`). In case (ii) that span is exactly `ℂe₀ ⊕ (B'^⊥ ⊗ ℂ)`, of dimension
  `N'`. It equals the span of `(e₀, (0, c'_m))` for a `ℚ`-basis `c' : Fin (N'−1) → Fin N' → ℚ` of
  `B'^⊥`. That family has the exact shape the proved `ellW_dichotomy`, `ellW_B_mem_span` and
  `one_le_ellW_false` consume, at level `r := N'`, when `N' ≥ 2`. The case `N' = 1` is a direct
  two-line computation. `ze_engine` is already stated for `ZEData N r` with `N ≤ r`, and when
  `N < r` the ρ = r exclusions (E2)/(E3) are never reached, because `ρ ≤ N' < r`. So the engine
  runs unchanged at level `N'`.

**`B_eq_zero_of_deg_lt_one` is TRUE, and it is already PROVED.**
* The file `Submission/Work/BW/B_eq_zero_of_deg_lt_one.lean` has no `sorry`. I elaborated it on
  3.144 today in 6 s with `lake env lean`: no errors, only unused-variable lint.
* `#print axioms` shows `sorryAx` only through the sibling `zero_estimate_stepwise` (P86*).
  `prim_basis_from_minors` and `ze_engine` are axiom-clean.
* The review said "either true-vacuously or false". It is the first: when `B i ≠ 0` the
  hypotheses are inconsistent. That inconsistency is exactly the content we need, so the lemma is
  useful and not a defect.
* Its proof: `quotient_reduction` shows that `(e₀, (0, c_m ∘ σ))` spans all of `ℂ^{N'+1}`, since
  `B^⊥ + ℚ^{Deg} = ℚ^r` when `B|_Deg ≠ 0`. Then `ellW = k` for every subgroup the zero estimate
  can return, and `transversal_exclusion_spec` rules out every `ℓ = k` output by (E0)/(E1).
  The ellW = k exclusions do not need `B` or `hΛ`, so no reduced linear form is needed.
* Consequence: in the degenerate case, `B` vanishes on `Deg`. Case (i) never has to be treated
  again; `mp_degenerate` simply calls this lemma.

## 2. Mathematics of case (ii)

**Setting.** `B|_Deg = 0` and `B ≠ 0`. So `range σ ≠ ∅`, `1 ≤ N' < r`, and `B' ≠ 0`.

**Step 1: Reduction.** `P` has degree `0` in `Y_{k+1}` for `k ∈ Deg`, so `P = rename (liftIdx σ) P'`
(`zeroDeg_reduce`). For every family `W` on `G`,
`eval (ptS ℓ s) (applyW W t P) = eval (ptTheta (exp∘ℓ∘σ) s) (applyW (W ∘ liftIdx σ) t P')`.
So `hvan` becomes the vanishing hypothesis of `zero_estimate_stepwise` at level `N'`, with
`w = (e₀, (0, c_m ∘ σ))` (`q = r−1+1`) and `D = ⌊𝒟 ∘ liftIdx σ⌋ ≥ 1`. This is the proof of
`quotient_reduction` with the span bullet deleted.

**Step 2: The hypothesis package `ZEData N' r`.**
* The data: `δ = 𝒟 ∘ liftIdx σ`, `B'`, `ℓ'`.
* (E0): immediate from `hE0 (σ j)`.
* (E1): `hE1_extend`. The factor `(r+1)!/(r−m)!` stays at the ambient `r`, which is what the
  engine's `descFactorial_le` expects.
* (E2)/(E3): vacuous, because `N' ≠ r`.
* `ℓ'` is `ℚ`-independent, since `σ` is injective.
* `hΛ` transfers exactly, because `∑ B'_j ℓ'_j = ∑ B_i ℓ_i` when `B|_Deg = 0`.
* `hSsum` holds because the sum runs over fewer steps.

**Step 3: The Lie algebra.**
* `span_ℚ {c_m ∘ σ} = B'^⊥` (in `ℚ^{N'}`):
  * `⊆`: `⟨c_m∘σ, B'⟩ = ⟨c_m, B⟩ = 0`, since `B|_Deg = 0`.
  * `⊇`: take `v ⊥ B'`. Extending by zero gives `ṽ = extend σ v 0 ⊥ B`. Since `B^⊥ = span_ℚ c`
    (`r − 1` independent vectors in an `(r−1)`-dimensional space), `ṽ = ∑ μ_m c_m`. Restricting
    along `σ` gives `v = ∑ μ_m (c_m∘σ)`.
* Hence `span_ℂ(range w) = ℂe₀ ⊕ span_ℂ(B'^⊥) = span_ℂ(range w')` with
  `w' = (e₀, (0, c'_m))_{m < N'−1}` and `c'` a `ℚ`-basis of `B'^⊥` (`finrank B'^⊥ = N' − 1`).
* `ellW w ε M = ellW w' ε M`, by `rw` of the spans inside `ellW`.

**Step 4: The dichotomy, positivity and good-case identification at level `N'`.**
* **`N' ≥ 2`:** `ellW_dichotomy (r := N') c'`, `one_le_ellW_false (r := N') c'` and
  `ellW_B_mem_span (r := N') c' B'`. `hcB` for `c'` holds by construction; `1 ≤ ρ` in the good
  case comes from `hε` for `ε = true`, and from positivity for `ε = false`.
* **`N' = 1`:**
  * `B'^⊥ = 0`, so every `c_m(σ 0) = 0` and `span w = ℂe₀`.
  * `e₀ ∈ lieSub 1 ρ ε M` iff `ε = true`, because the `M`-conditions only see the coordinates
    `succ`.
  * So `ellW = 0` if `ε = true`, forcing `ρ = 1` and `k = 1`, and `ellW = 1` if `ε = false`,
    giving `k = 1 + ρ` with `ρ ∈ {0, 1}`. The dichotomy and positivity follow.
  * The good case forces `ρ = 1`. Then `M 0 ∈ ℤ^1` is nonzero, its `ℚ`-span is `⊤`, and
    `B' ∈ ⊤`.

**Step 5: The engine.**
* `ze_engine (D : ZEData N' r)` receives:
  * the zero-estimate output at level `N'`;
  * `hLdich`, `hLpos` and `hGoodB` from step 4;
  * `hmin` from `prim_basis_from_minors (r := N')`, with the `ρ = 0` case exactly as in `mp_main`.
* It returns `ρ` with `1 ≤ ρ < r`. For all `a' > 0` it gives a primitive `M'` on `Fin N'` with
  `B' ∈ ℚ-span M'`, and `J' ⊆ Fin N'` with the case-A/B inequality, **already with the ambient
  constants `constA r ρ` / `constB r ρ`** and `δ i.succ = 𝒟 (σ i).succ`.
* Why the induction measure drops, if one asks: the ambient dimension goes from `r` to `N' < r`.
  But no induction is actually needed. The engine at level `N'` is applied once, and its outputs
  with `ρ = N'` ("`G_a × 1`" and "`0 × 1`" of the quotient) are legitimate, since
  `N' < r = the bound on ρ`.

**Step 6: Pull back.** Given `a > 0` on `Fin r`, set `a' = a ∘ σ`, `M = extM σ M'` and
`J = J'.map σ`.
* `PrimSys` comes from `extM_primSys`.
* `B ∈ ℚ-span M` comes from `mem_span_extM`, which needs `B|_Deg = 0`.
* `∏_j ∑_i a_i|M_ji| = ∏_j ∑_i a'_i|M'_ji|` comes from `extM_sum_abs`.
* `∏_{i∈J} a_i 𝒟_{i+1} = ∏_{i∈J'} a'_i δ_{i+1}` comes from `Finset.prod_map`, `hδeq` and
  `liftIdx σ i.succ = (σ i).succ` (`rfl`, `zeroDeg_liftIdx_succ`).
* `δ 0 = 𝒟 0`.

## 3. The lemmas (one `.stmt` each in this directory)

| # | name | content | size | proof sketch |
|---|---|---|---|---|
| 1 | `quotient_reduction_core` | step 1 without `B`: outputs `N' < r`, `StrictMono σ`, `∀ k ∉ range σ, 𝒟 k.succ < 1`, `P'`, `δ`, `w`, degree and vanishing | 0.2–0.4k | Copy `quotient_reduction`'s proof. `σ := (univ.filter (1 ≤ 𝒟 ·.succ)).orderEmbOfFin rfl`. Delete the `span = ⊤` bullet and the `B`/`hker`/`hBi` arguments. The new conjuncts are `hσmono` and `hσlt`, which the old proof already builds. |
| 2 | `reduced_span_eq` | a `ℚ`-basis `c'` of `(B∘σ)^⊥` with `span_ℂ (range w) = span_ℂ (range (e₀,(0,c')))` | 0.5–1k | Step 3. `K := LinearMap.ker (∑ⱼ B(σ j) • proj j)` over `ℚ`, `finrank K = N' − 1` (rank–nullity, the functional ≠ 0). `c' := Module.finBasisOfFinrankEq ℚ K h` coerced. For `B^⊥ ⊆ span c`: `span c ≤ B^⊥` by `hcB`, equal finrank `r − 1` (`finrank_span_eq_card hc`), `Submodule.eq_of_le_of_finrank_eq`. Extension and restriction via `Function.extend σ · 0` and `zeroDeg_sum_range_eq` (as in `qr_rat_rows_span`). ℚ→ℂ: a ℚ-combination `v = ∑ μ_m u_m` casts to `(0, v) = ∑ (μ_m:ℂ) • (0, u_m)`, so use `Submodule.span_le` + `Submodule.sum_mem`/`smul_mem` in both directions, with `e₀` matched to `e₀`. |
| 3 | `reduced_ellW_facts` | the dichotomy, `1 ≤ ellW` for `ε = false`, and `ellW = k−1 → B∘σ ∈ ℚ-span M` | 0.4–0.8k | `ellW w = ellW w'` by `unfold ellW; rw [span_eq]` (lemma 2). **N' ≥ 2:** `ellW_dichotomy (r := N')` then the `omega` conversion of `ldich_of_dichotomy`; `one_le_ellW_false`; `ellW_B_mem_span (r := N') (B := B∘σ)`, with `B∘σ ≠ 0` from `hB` + `hBZ` and `1 ≤ ρ` from `hε` or positivity. **N' = 1:** from `hBZ`, `hcB` and `B(σ 0) ≠ 0`, `c m (σ 0) = 0`, so `span w = span {e₀}`, finrank 1. `e₀ ∈ lieSub` ↔ `ε` (unfold `lieSub`: `proj 0 e₀ = 1`, `proj i.succ e₀ = 0`). So `span ⊓ lieSub` is `span{e₀}` or `⊥`, giving `ellW ∈ {0, 1}` as in §2 step 4. Good case: `ρ = 1`, `M 0 0 ≠ 0` (lin. indep.), so `span_ℚ {M 0} = ⊤` in `ℚ^1`. |
| 4 | `mp_pullback` | level-`N'` conclusion ⇒ level-`r` conclusion | 0.3–0.5k | Step 6. `⟨ρ, h1, h2, fun a ha => …⟩`: apply `h` to `a ∘ σ`, then `extM σ M'`, `extM_primSys`, `mem_span_extM σ hσ M' B hBZ`, `J'.map ⟨σ, hσ⟩` (`Finset.card_map`), `extM_sum_abs`, `Finset.prod_map`, `hδeq`. `Or.imp` on the two cases. |
| 5 | `mp_degenerate` | the degenerate branch | **done, below** | Verified assembly over lemmas 1–4 (sorried) plus the proved siblings. |

**`mp_degenerate`'s proof and the final `multiplicity_prop` proof were both elaborated on 3.144**
in a scratch file (`/tmp/bwmp_design/MPTest3.lean`, importing `multiplicity_prop`,
`B_eq_zero_of_deg_lt_one`, `prim_basis_from_minors`, `hE1_extend`, `zeroDeg_reduce`, `DefsMP`).
The result was: `sorry` warnings **only** on lemmas 1–4, and no errors. So once lemmas 1–4 land,
`multiplicity_prop` is closed.

The proof of `mp_degenerate` (to be pasted after its statement; the file needs imports of
`multiplicity_prop` or its pieces, `B_eq_zero_of_deg_lt_one`, `prim_basis_from_minors`,
`hE1_extend`, `zeroDeg_reduce`, and lemmas 1–4):

```lean
  classical
  obtain ⟨i, hi⟩ := hdg
  have hBZdeg : ∀ k : Fin r, 𝒟 k.succ < 1 → B k = 0 := fun k hk =>
    B_eq_zero_of_deg_lt_one hr P hP 𝒟 hdeg h𝒟0 𝒮 𝒯 Sq Tq hSa hTa hSsum hTsum hE0 hE1 hE2 hE3
      B hB c hc hcB ℓ hℓ hΛ hvan k hk
  obtain ⟨N', σ, P', δ, w, hN'lt, hσmono, hσdeg, hP'ne, hδnn, hδ0, hδ1, hdeg', hδeq, hw1, hw0,
      hvan'⟩ := quotient_reduction_core P hP 𝒟 hdeg h𝒟0 Sq Tq 𝒮 𝒯 hSsum hTsum c ℓ hvan i hi
  have hσinj : Function.Injective σ := hσmono.injective
  have hBZ : ∀ k, k ∉ Set.range σ → B k = 0 := fun k hk => hBZdeg k (hσdeg k hk)
  have hBσ : (fun j => B (σ j)) ≠ 0 := by
    intro h0; apply hB; funext k
    by_cases hk : k ∈ Set.range σ
    · obtain ⟨j, rfl⟩ := hk; exact congr_fun h0 j
    · exact hBZ k hk
  have hΛσ : ‖∑ j, ((B (σ j) : ℤ) : ℂ) * ℓ (σ j)‖ < Real.pi / 𝒮 := by
    have h : ∑ k, (B k : ℂ) * ℓ k = ∑ j, ((B (σ j) : ℤ) : ℂ) * ℓ (σ j) :=
      zeroDeg_sum_range_eq σ hσinj (fun k => (B k : ℂ) * ℓ k) (fun k hk => by simp [hBZ k hk])
    rw [← h]; exact hΛ
  have hSpos : 0 < 𝒮 := Spos_of_hLambda B ℓ 𝒮 hΛ
  have hsub : Finset.range (N' + 1) ⊆ Finset.range (r + 1) := Finset.range_mono (by omega)
  have hSsum' : ((∑ m ∈ Finset.range (N' + 1), Sq m : ℕ) : ℝ) ≤ 𝒮 :=
    le_trans (by exact_mod_cast Finset.sum_le_sum_of_subset hsub) hSsum
  have hE1δ : ∀ m, m < r → ∀ e : Fin (N' + 1) → ℕ, (∀ i, e i ≤ 1) → ∑ i, e i = m + 1 →
      ((r + 1).descFactorial (m + 1) : ℝ) * ∏ i, δ i ^ e i <
        ((Sq m : ℝ) + 1) * ((Tq m + m + 1).choose (m + 1) : ℝ) := by
    intro m hm e he hs
    have h := hE1_extend σ hσmono 𝒟 Sq Tq m hm hE1 e he hs
    simpa only [← hδeq] using h
  let D : ZEData N' r :=
    { hNr := hN'lt.le, hr := hr, δ := δ, hδnn := hδnn, hδ0 := hδ0, hδ1 := hδ1, 𝒮 := 𝒮,
      hSpos := hSpos, Sq := Sq, Tq := Tq, hSa := fun m hm => hSa m (by omega),
      hTa := fun m hm => hTa m (by omega), hSsum := hSsum',
      hE0 := fun j => by rw [hδeq, zeroDeg_liftIdx_succ]; exact hE0 (σ j),
      hE1 := hE1δ, hE2 := fun h => absurd h (by omega), hE3 := fun h => absurd h (by omega),
      B := fun j => B (σ j), hB := hBσ, ℓ := fun j => ℓ (σ j), hℓ := hℓ.comp σ hσinj,
      hΛ := hΛσ }
  obtain ⟨ε, ρ, M, hρN, hM, hε0, m, hm, hineq⟩ :=
    zero_estimate_stepwise (N := N') (q := r - 1 + 1) P' hP'ne (fun j => ⌊δ j⌋₊) hδ1 hdeg' w
      (fun j => Complex.exp (ℓ (σ j))) (fun j => Complex.exp_ne_zero _) Sq Tq hvan'
  obtain ⟨hLdich, hLpos, hGoodB⟩ :=
    reduced_ellW_facts σ hσinj c hc B hB hcB hBZ w hw0 hw1 hρN M hM ε hε0
  have hminr : ∀ (a : Fin N' → ℝ), (∀ i, 0 < a i) →
      ∀ (J₀ : Finset (Fin N')) (hJ₀ : J₀.card = ρ),
        (∀ (I : Finset (Fin N')) (hI : I.card = ρ),
          |(minorJ M I hI : ℝ)| * ∏ i ∈ I, a i ≤ |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i) →
        ∃ M' : Fin ρ → Fin N' → ℤ, PrimSys M' ∧
          Submodule.span ℤ (Set.range M') = Submodule.span ℤ (Set.range M) ∧
          (∏ j, ∑ i, a i * |(M' j i : ℝ)|) ≤
            (2 : ℝ) ^ (1 - (ρ : ℤ)) * (ρ.factorial : ℝ) ^ 2 * (N' : ℝ) ^ ρ *
              |(minorJ M J₀ hJ₀ : ℝ)| * ∏ i ∈ J₀, a i := by
    intro a ha J₀ hJ₀ hmax
    rcases Nat.eq_zero_or_pos ρ with h0 | hρ1
    · subst h0
      refine ⟨M, hM, rfl, ?_⟩
      have hΔ : minorJ M J₀ hJ₀ = 1 := minorJ_zero hJ₀ hJ₀
      have hJ0' : J₀ = ∅ := Finset.card_eq_zero.mp hJ₀
      have hleft : (∏ j : Fin 0, ∑ i : Fin N', a i * |(M j i : ℝ)|) = 1 := by simp
      rw [hleft, hΔ, hJ0']
      norm_num
    · exact prim_basis_from_minors hρ1 hρN M hM a ha J₀ hJ₀ hmax
  have hout := ze_engine D ε ρ M m (ellW w ε M) hρN hM hε0 hm hLdich hLpos hGoodB hminr hineq
  exact mp_pullback σ hσinj 𝒟 δ hδeq Sq Tq B hBZ hout
```

The final `multiplicity_prop` proof (replaces `:= by sorry` at line 825):

```lean
  by_cases hnd : ∀ j : Fin r, 1 ≤ 𝒟 j.succ
  · exact mp_main hr P hP 𝒟 hdeg h𝒟0 𝒮 𝒯 Sq Tq hSa hTa hSsum hTsum hnd hE0 hE1 hE2 hE3 B hB c hc
      hcB ℓ hℓ hΛ hvan (fun ρ h1 h2 M hM a ha J hJ hmax =>
        prim_basis_from_minors h1 h2 M hM a ha J hJ hmax)
  · push_neg at hnd   -- works (deprecation lint only); or `push Not at hnd`
    exact mp_degenerate hr P hP 𝒟 hdeg h𝒟0 𝒮 𝒯 Sq Tq hSa hTa hSsum hTsum hE0 hE1 hE2 hE3 B hB c
      hc hcB ℓ hℓ hΛ hvan hnd
```

**Placement.**
* `mp_degenerate` needs `mp_main`'s file only for `Spos_of_hLambda` and `minorJ_zero`.
* Simplest placement: put lemmas 1–4 in their own modules, and put `mp_degenerate` plus the final
  proof at the bottom of `multiplicity_prop.lean`, importing the four modules together with
  `B_eq_zero_of_deg_lt_one`, `prim_basis_from_minors`, `hE1_extend` and `zeroDeg_reduce`.
* Import cycle check: `B_eq_zero_of_deg_lt_one` imports `multiplicity_engine`, not
  `multiplicity_prop`, so there is no cycle.

## 4. Risks

* **Low overall.** Every hard analytic step is already proved: (E)-table, collision analysis, the
  full-span contradiction (`B_eq_zero_of_deg_lt_one`), and Minkowski (`prim_basis_from_minors`).
  The remaining lemmas are linear algebra and reindexing.
* **The largest remaining item is lemma 2.** It needs ℚ→ℂ span bookkeeping and the finrank of a
  hyperplane. That is mechanical, but `Fin.cons`-typed families can be fiddly. Suggestion: first
  prove `span_ℂ (range w) = span_ℂ ({e₀} ∪ range (fun v : K => (0, cast v)))` for both families,
  then compare.
* **Lemma 3 at `N' = 1`.** This is a separate small computation. It is needed because
  `ellW_dichotomy` requires `2 ≤ r`. Do not skip it: `N' = 1` really occurs, for example `r = 2`
  with one degenerate coordinate.
* **The only unproved input under all of this is the sibling `zero_estimate_stepwise` (P86\*).**
  It carries `sorryAx` into `B_eq_zero_of_deg_lt_one` and `mp_main` alike.
-/

namespace Work.BW

/-- Casting a `ℚ`-linear combination to `ℂ`. -/
private lemma rat_cast_mem_span {n : ℕ} {ι : Type*} (v : ι → Fin n → ℚ) (x : Fin n → ℚ)
    (hx : x ∈ Submodule.span ℚ (Set.range v)) :
    (fun j : Fin n => ((x j : ℚ) : ℂ)) ∈
      Submodule.span ℂ (Set.range fun m : ι => fun j : Fin n => ((v m j : ℚ) : ℂ)) := by
  refine Submodule.span_induction (p := fun x _ =>
      (fun j : Fin n => ((x j : ℚ) : ℂ)) ∈
        Submodule.span ℂ (Set.range fun m : ι => fun j : Fin n => ((v m j : ℚ) : ℂ)))
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    obtain ⟨m, rfl⟩ := hx
    exact Submodule.subset_span ⟨m, rfl⟩
  · have h0 : (fun j : Fin n => (((0 : Fin n → ℚ) j : ℚ) : ℂ)) = (0 : Fin n → ℂ) := by
      funext j; simp
    rw [h0]
    exact Submodule.zero_mem (Submodule.span ℂ
      (Set.range fun m : ι => fun j : Fin n => ((v m j : ℚ) : ℂ)))
  · intro x y hx hy ihx ihy
    have h : (fun j : Fin n => (((x + y) j : ℚ) : ℂ))
        = (fun j : Fin n => ((x j : ℚ) : ℂ)) + (fun j : Fin n => ((y j : ℚ) : ℂ)) := by
      funext j; simp only [Pi.add_apply, Rat.cast_add]
    rw [h]; exact Submodule.add_mem _ ihx ihy
  · intro a x hx ihx
    have h : (fun j : Fin n => (((a • x) j : ℚ) : ℂ))
        = (a : ℂ) • (fun j : Fin n => ((x j : ℚ) : ℂ)) := by
      funext j; simp only [Pi.smul_apply, smul_eq_mul, Rat.cast_mul]
    rw [h]; exact Submodule.smul_mem _ _ ihx

/-- The inclusion `ℂ^{n} → ℂ^{n+1}`, `u ↦ (0, u)`. -/
private def dConsL (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun u := Fin.cons 0 u
  map_add' x y := by funext i; refine Fin.cases ?_ ?_ i <;> simp
  map_smul' a x := by funext i; refine Fin.cases ?_ ?_ i <;> simp

/-- The three facts `ze_engine` needs about `L = ellW w ε M` for the restricted family
`w = (e₀, (0, c m ∘ σ))` at level `N'`, when `B` vanishes off `range σ`: the dichotomy
`L ∈ {k - 1, k}` (`k = (if ε then 0 else 1) + ρ`), `1 ≤ L` for `ε = false`, and
`L = k - 1 → B ∘ σ ∈ ℚ-span M`. -/
theorem reduced_ellW_facts {r N' ρ : ℕ} (σ : Fin N' → Fin r) (hσ : Function.Injective σ)
    (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (B : Fin r → ℤ) (hB : B ≠ 0) (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0)
    (hBZ : ∀ k : Fin r, k ∉ Set.range σ → B k = 0)
    (w : Fin (r - 1 + 1) → Fin (N' + 1) → ℂ)
    (hw0 : w 0 = Pi.single (0 : Fin (N' + 1)) (1 : ℂ))
    (hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun j : Fin N' => ((c m (σ j) : ℚ) : ℂ)))
    (hρN : ρ ≤ N') (M : Fin ρ → Fin N' → ℤ) (hM : PrimSys M) (ε : Bool)
    (hε : ¬ (ε = true ∧ ρ = 0)) :
    (ellW w ε M = (if ε then 0 else 1) + ρ - 1 ∨ ellW w ε M = (if ε then 0 else 1) + ρ) ∧
    (ε = false → 1 ≤ ellW w ε M) ∧
    (ellW w ε M = (if ε then 0 else 1) + ρ - 1 →
      (fun j => (B (σ j) : ℚ)) ∈ Submodule.span ℚ (Set.range fun k j => (M k j : ℚ))) := by
  classical
  have hB' : (fun j : Fin N' => B (σ j)) ≠ 0 := by
    intro h0
    apply hB
    funext k
    by_cases hk : k ∈ Set.range σ
    · obtain ⟨j, rfl⟩ := hk
      simpa using congr_fun h0 j
    · exact hBZ k hk
  have hq_ne : (fun j : Fin N' => (B (σ j) : ℚ)) ≠ 0 := by
    intro h0
    apply hB'
    funext j
    have h1 := congr_fun h0 j
    simp only [Pi.zero_apply] at h1
    exact_mod_cast h1
  have hN'pos : 1 ≤ N' := by
    rcases Nat.eq_zero_or_pos N' with h0 | hpos
    · exfalso
      apply hq_ne
      funext j
      exact Fin.elim0 (Fin.cast h0 j)
    · exact hpos
  have hcBσ : ∀ m : Fin (r - 1), ∑ j : Fin N', c m (σ j) * (B (σ j) : ℚ) = 0 := by
    intro m
    have hG : ∀ i : Fin r, i ∉ Set.range σ → c m i * (B i : ℚ) = 0 := by
      intro i hi; rw [hBZ i hi, Int.cast_zero, mul_zero]
    rw [← zeroDeg_sum_range_eq σ hσ (fun i => c m i * (B i : ℚ)) hG]
    exact hcB m
  have hM_indep : LinearIndependent ℚ (fun j i => (M j i : ℚ)) := hM.1
  by_cases h2 : 2 ≤ N'
  · -- ## general case, `N' ≥ 2`
    let β : Fin N' → ℚ := fun j => (B (σ j) : ℚ)
    have hβ_ne : β ≠ 0 := hq_ne
    let θ : (Fin N' → ℚ) →ₗ[ℚ] ℚ :=
      ∑ j, β j • LinearMap.proj (R := ℚ) (φ := fun _ : Fin N' => ℚ) j
    have hθ : ∀ v : Fin N' → ℚ, θ v = ∑ j, β j * v j := by
      intro v
      simp only [θ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
    let K : Submodule ℚ (Fin N' → ℚ) := LinearMap.ker θ
    have hKmem : ∀ v : Fin N' → ℚ, v ∈ K ↔ ∑ j, β j * v j = 0 := by
      intro v
      change v ∈ LinearMap.ker θ ↔ ∑ j, β j * v j = 0
      rw [LinearMap.mem_ker, hθ v]
    have hθtop : LinearMap.range θ = ⊤ := by
      obtain ⟨j₀, hj₀⟩ : ∃ j : Fin N', β j ≠ 0 := by
        by_contra h
        push Not at h
        exact hβ_ne (funext fun j => h j)
      rw [Submodule.eq_top_iff']
      intro c₀
      have hsingle : θ (Pi.single j₀ (1 : ℚ)) = β j₀ := by
        rw [hθ]
        rw [Finset.sum_eq_single j₀]
        · simp
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_univ j₀) h
      have hmem : (c₀ / β j₀) • θ (Pi.single j₀ (1 : ℚ)) ∈ LinearMap.range θ :=
        Submodule.smul_mem _ _ (LinearMap.mem_range.mpr ⟨_, rfl⟩)
      rw [hsingle, smul_eq_mul] at hmem
      have hc₀ : (c₀ / β j₀) * β j₀ = c₀ := div_mul_cancel₀ c₀ hj₀
      rwa [hc₀] at hmem
    have hfinK : Module.finrank ℚ K = N' - 1 := by
      have h := LinearMap.finrank_range_add_finrank_ker θ
      rw [hθtop] at h
      simp only [finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
        Fintype.card_fin] at h
      change Module.finrank ℚ (LinearMap.ker θ) = N' - 1
      omega
    let cb : Module.Basis (Fin (N' - 1)) ℚ K := Module.finBasisOfFinrankEq ℚ K hfinK
    let c' : Fin (N' - 1) → Fin N' → ℚ := fun m => (cb m : Fin N' → ℚ)
    have hc'_indep : LinearIndependent ℚ c' := by
      have h := cb.linearIndependent.map' (Submodule.subtype K) (Submodule.ker_subtype K)
      convert h using 1
      ext m
      rfl
    have hspanK : Submodule.span ℚ (Set.range c') = K := by
      have h := congrArg (Submodule.map (Submodule.subtype K)) cb.span_eq
      rw [Submodule.map_span, Submodule.map_subtype_top] at h
      rw [← h]
      congr 1
      ext x
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨cb m, ⟨m, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨m, rfl⟩, rfl⟩
        exact ⟨m, rfl⟩
    have hc'B : ∀ m : Fin (N' - 1), ∑ j : Fin N', c' m j * β j = 0 := by
      intro m
      have hm : c' m ∈ K := (cb m).2
      have h0 : ∑ j, β j * c' m j = 0 := (hKmem (c' m)).mp hm
      rw [← h0]
      exact Finset.sum_congr rfl fun j _ => by ring
    let u : Fin (r - 1) → Fin N' → ℂ := fun m j => ((c m (σ j) : ℚ) : ℂ)
    let u' : Fin (N' - 1) → Fin N' → ℂ := fun m j => ((c' m j : ℚ) : ℂ)
    have hS : Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range u') := by
      refine le_antisymm ?_ ?_
      · apply Submodule.span_le.mpr
        rintro x ⟨m, rfl⟩
        have hm : (fun j : Fin N' => c m (σ j)) ∈ Submodule.span ℚ (Set.range c') := by
          rw [hspanK, hKmem]
          rw [← hcBσ m]
          exact Finset.sum_congr rfl fun j _ => by ring
        exact rat_cast_mem_span c' (fun j : Fin N' => c m (σ j)) hm
      · apply Submodule.span_le.mpr
        rintro x ⟨m, rfl⟩
        have hm : c' m ∈ Submodule.span ℚ
            (Set.range fun m' : Fin (r - 1) => fun j : Fin N' => c m' (σ j)) :=
          reduced_orth_mem_span σ hσ c hc B hB hcB hBZ (c' m) (by
            rw [← hc'B m]
            exact Finset.sum_congr rfl fun j _ => by ring)
        exact rat_cast_mem_span (fun m' : Fin (r - 1) => fun j : Fin N' => c m' (σ j)) (c' m) hm
    let w' : Fin (N' - 1 + 1) → Fin (N' + 1) → ℂ :=
      Fin.cons (Pi.single (0 : Fin (N' + 1)) (1 : ℂ))
        (fun m : Fin (N' - 1) => Fin.cons 0 (fun j : Fin N' => ((c' m j : ℚ) : ℂ)))
    have hw0' : w' 0 = Pi.single (0 : Fin (N' + 1)) (1 : ℂ) := Fin.cons_zero _ _
    have hw1' : ∀ m : Fin (N' - 1), w' m.succ =
        Fin.cons 0 (fun j : Fin N' => ((c' m j : ℚ) : ℂ)) := fun m => Fin.cons_succ _ _ _
    have hspan : Submodule.span ℂ (Set.range w) = Submodule.span ℂ (Set.range w') := by
      refine le_antisymm ?_ ?_
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · rw [hw0]
          exact Submodule.subset_span ⟨0, hw0'⟩
        · rw [hw1 m]
          change dConsL N' (u m) ∈ Submodule.span ℂ (Set.range w')
          have hum : u m ∈ Submodule.span ℂ (Set.range u') := by
            rw [← hS]; exact Submodule.subset_span ⟨m, rfl⟩
          have hmem : dConsL N' (u m) ∈
              Submodule.map (dConsL N') (Submodule.span ℂ (Set.range u')) := ⟨u m, hum, rfl⟩
          rw [Submodule.map_span] at hmem
          refine Submodule.span_mono ?_ hmem
          rintro y ⟨z, ⟨m', rfl⟩, rfl⟩
          exact ⟨m'.succ, by rw [hw1' m']; rfl⟩
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · rw [hw0']
          exact Submodule.subset_span ⟨0, hw0⟩
        · rw [hw1' m]
          change dConsL N' (u' m) ∈ Submodule.span ℂ (Set.range w)
          have hum : u' m ∈ Submodule.span ℂ (Set.range u) := by
            rw [hS]; exact Submodule.subset_span ⟨m, rfl⟩
          have hmem : dConsL N' (u' m) ∈
              Submodule.map (dConsL N') (Submodule.span ℂ (Set.range u)) := ⟨u' m, hum, rfl⟩
          rw [Submodule.map_span] at hmem
          refine Submodule.span_mono ?_ hmem
          rintro y ⟨z, ⟨m', rfl⟩, rfl⟩
          exact ⟨m'.succ, by rw [hw1 m']; rfl⟩
    have hellW : ellW w ε M = ellW w' ε M := by
      unfold ellW
      rw [hspan]
    have hdish : ellW w' ε M = (if ε then 0 else 1) + ρ - 1 ∨
        ellW w' ε M = (if ε then 0 else 1) + ρ := by
      have h := ellW_dichotomy (r := N') (ρ := ρ) h2 hρN c' hc'_indep M hM_indep ε w' hw0' hw1'
      rcases h with h | h
      · left; rw [h]
        rcases ε with _ | _ <;> simp only [Bool.false_eq_true, reduceIte] <;> omega
      · right; rw [h]
        rcases ε with _ | _ <;> simp only [Bool.false_eq_true, reduceIte] <;> omega
    have hdich : ellW w ε M = (if ε then 0 else 1) + ρ - 1 ∨
        ellW w ε M = (if ε then 0 else 1) + ρ := by
      rw [hellW]; exact hdish
    have hpos : ε = false → 1 ≤ ellW w ε M := by
      intro hεf
      rw [hεf]
      have he0W : (Pi.single (0 : Fin (N' + 1)) (1 : ℂ) : Fin (N' + 1) → ℂ) ∈
          Submodule.span ℂ (Set.range w) := Submodule.subset_span ⟨0, hw0⟩
      have he0L : (Pi.single (0 : Fin (N' + 1)) (1 : ℂ) : Fin (N' + 1) → ℂ) ∉
          lieSub N' ρ false M := by
        intro hmem
        have hle : lieSub N' ρ false M ≤
            LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (N' + 1) => ℂ) 0) := by
          simp only [lieSub, Bool.false_eq_true, ite_false]
          exact inf_le_left
        have hker := hle hmem
        rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at hker
        exact one_ne_zero hker
      unfold ellW
      have hle : (Submodule.span ℂ (Set.range w) ⊓ lieSub N' ρ false M :
            Submodule ℂ (Fin (N' + 1) → ℂ)) ≤ Submodule.span ℂ (Set.range w) := inf_le_left
      have hne : (Submodule.span ℂ (Set.range w) ⊓ lieSub N' ρ false M :
            Submodule ℂ (Fin (N' + 1) → ℂ)) ≠ Submodule.span ℂ (Set.range w) := by
        intro h
        have hmem : (Pi.single (0 : Fin (N' + 1)) (1 : ℂ) : Fin (N' + 1) → ℂ) ∈
            Submodule.span ℂ (Set.range w) ⊓ lieSub N' ρ false M := by rw [h]; exact he0W
        exact he0L (Submodule.mem_inf.mp hmem).2
      have hlt : Module.finrank ℂ (Submodule.span ℂ (Set.range w) ⊓ lieSub N' ρ false M :
            Submodule ℂ (Fin (N' + 1) → ℂ))
          < Module.finrank ℂ (Submodule.span ℂ (Set.range w)) := by
        by_contra h
        rw [not_lt] at h
        exact hne (Submodule.eq_of_le_of_finrank_le hle h)
      omega
    have hgood : ellW w ε M = (if ε then 0 else 1) + ρ - 1 →
        (fun j => (B (σ j) : ℚ)) ∈ Submodule.span ℚ (Set.range fun k j => (M k j : ℚ)) := by
      intro hL
      have hρ1 : 1 ≤ ρ := by
        cases ε with
        | true =>
          by_contra h
          push Not at h
          exact hε ⟨rfl, by omega⟩
        | false =>
          have hp := hpos rfl
          rw [hL] at hp
          simpa using hp
      have hℓ' : ellW w' ε M = (if ε then ρ else ρ + 1) - 1 := by
        rw [← hellW, hL]
        rcases ε with _ | _ <;> simp only [Bool.false_eq_true, reduceIte] <;> omega
      exact ellW_B_mem_span (r := N') (ρ := ρ) h2 hρ1 hρN c' hc'_indep M hM_indep
        (fun j => B (σ j)) hB' hc'B ε w' hw0' hw1' hℓ'
    exact ⟨hdich, hpos, hgood⟩
  · -- ## case `N' = 1`
    have hN'1 : N' = 1 := by omega
    subst hN'1
    have hBσ0 : B (σ 0) ≠ 0 := by
      intro h0
      apply hB
      funext k
      simp only [Pi.zero_apply]
      by_cases hk : k ∈ Set.range σ
      · obtain ⟨j, hj⟩ := hk
        have hj0 : j = 0 := Subsingleton.elim j 0
        rw [hj0] at hj
        rw [← hj, h0]
      · exact hBZ k hk
    have hc0 : ∀ m : Fin (r - 1), c m (σ 0) = 0 := by
      intro m
      have h := hcBσ m
      simp only [Fin.sum_univ_one] at h
      rcases mul_eq_zero.mp h with h1 | h2
      · exact h1
      · exact absurd h2 (by exact_mod_cast hBσ0)
    have hwzero : ∀ m : Fin (r - 1), w m.succ = 0 := by
      intro m
      rw [hw1 m]
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp
      · simp only [Fin.cons_succ, Pi.zero_apply]
        rw [show j = 0 from Subsingleton.elim j 0]
        simp [hc0 m]
    have hspan_w : Submodule.span ℂ (Set.range w)
        = Submodule.span ℂ ({Pi.single (0 : Fin 2) (1 : ℂ)} : Set (Fin 2 → ℂ)) := by
      refine le_antisymm ?_ ?_
      · apply Submodule.span_le.mpr
        rintro x ⟨i, rfl⟩
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · rw [hw0]
          exact Submodule.subset_span (by simp)
        · rw [hwzero m]
          exact Submodule.zero_mem _
      · apply Submodule.span_le.mpr
        rintro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact Submodule.subset_span ⟨0, hw0⟩
    have he0ne : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ≠ 0 := by
      intro h
      have h1 := congr_fun h 0
      simp only [Pi.zero_apply] at h1
      rw [Pi.single_eq_same] at h1
      exact one_ne_zero h1
    have hfinW : Module.finrank ℂ (Submodule.span ℂ (Set.range w)) = 1 := by
      rw [hspan_w, finrank_span_singleton he0ne]
    have he0_iInf : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ∈
        (⨅ j : Fin ρ, LinearMap.ker
          (∑ i : Fin 1, ((M j i : ℂ)) •
            LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) i.succ)) := by
      rw [Submodule.mem_iInf]
      intro j
      rw [LinearMap.mem_ker]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply]
      rw [Fin.sum_univ_one]
      simp
    have he0_lieSub : ∀ δ : Bool, (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ∈
        lieSub 1 ρ δ M ↔ δ = true := by
      intro δ
      have hiff : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ∈ lieSub 1 ρ δ M ↔
          (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ∈ (if δ then ⊤ else
            LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0)) := by
        rw [lieSub]
        constructor
        · intro h; exact (Submodule.mem_inf.mp h).1
        · intro h; exact Submodule.mem_inf.mpr ⟨h, he0_iInf⟩
      rw [hiff]
      have he0ker : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ∉
          LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0) := by
        intro h
        rw [LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at h
        exact one_ne_zero h
      cases δ with
      | true => simp
      | false => simp [he0ker]
    have hinf_true : (Submodule.span ℂ (Set.range w) ⊓ lieSub 1 ρ true M :
        Submodule ℂ (Fin 2 → ℂ)) = Submodule.span ℂ (Set.range w) := by
      refine le_antisymm inf_le_left (le_inf le_rfl ?_)
      rw [hspan_w]
      apply Submodule.span_le.mpr
      rintro x hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact (he0_lieSub true).mpr rfl
    have hinf_false : (Submodule.span ℂ (Set.range w) ⊓ lieSub 1 ρ false M :
        Submodule ℂ (Fin 2 → ℂ)) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxW, hxL⟩ := Submodule.mem_inf.mp hx
      rw [hspan_w] at hxW
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxW
      by_cases ha0 : a = 0
      · rw [← ha, ha0, zero_smul]
      · exfalso
        have hmem : (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ) ∈ lieSub 1 ρ false M := by
          have h := Submodule.smul_mem (lieSub 1 ρ false M) a⁻¹ hxL
          rw [← ha] at h
          rw [smul_smul, inv_mul_cancel₀ ha0, one_smul] at h
          exact h
        exact Bool.false_ne_true ((he0_lieSub false).mp hmem)
    have hellW_true : ellW w true M = 0 := by
      unfold ellW
      rw [hinf_true, hfinW]
    have hellW_false : ellW w false M = 1 := by
      unfold ellW
      rw [hinf_false, hfinW]
      simp
    have hρ01 : ρ = 0 ∨ ρ = 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · rcases hρ01 with rfl | rfl
      · cases ε with
        | true => exact absurd ⟨rfl, rfl⟩ hε
        | false => right; simp [hellW_false]
      · cases ε with
        | true => left; simp [hellW_true]
        | false => left; simp [hellW_false]
    · intro hεf
      rw [hεf, hellW_false]
    · intro hL
      have hρ1 : ρ = 1 := by
        rcases hρ01 with h | h
        · subst h
          cases ε with
          | true => exact absurd ⟨rfl, rfl⟩ hε
          | false =>
            rw [hellW_false] at hL
            simp only [Bool.false_eq_true, reduceIte] at hL
            omega
        · exact h
      subst hρ1
      have hM0 : (M 0 0 : ℚ) ≠ 0 := by
        intro h0
        refine hM.1.ne_zero (0 : Fin 1) (funext fun i => ?_)
        simp only [Pi.zero_apply]
        rw [show i = 0 from Subsingleton.elim i 0]
        simpa using h0
      have htop : Submodule.span ℚ (Set.range fun k : Fin 1 => fun j : Fin 1 => (M k j : ℚ))
          = ⊤ := by
        have hrange : (Set.range fun k : Fin 1 => fun j : Fin 1 => (M k j : ℚ))
            = {(fun j : Fin 1 => (M 0 j : ℚ))} := by
          ext v
          constructor
          · rintro ⟨k, rfl⟩
            rw [show k = 0 from Subsingleton.elim k 0]
            exact Set.mem_singleton _
          · intro hv
            exact ⟨0, (Set.mem_singleton_iff.mp hv).symm⟩
        rw [hrange, Submodule.eq_top_iff']
        intro v
        rw [Submodule.mem_span_singleton]
        refine ⟨v 0 / ((M 0 0 : ℤ) : ℚ), ?_⟩
        funext j
        rw [show j = 0 from Subsingleton.elim j 0]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact div_mul_cancel₀ (v 0) hM0
      rw [htop]
      exact Submodule.mem_top

end Work.BW

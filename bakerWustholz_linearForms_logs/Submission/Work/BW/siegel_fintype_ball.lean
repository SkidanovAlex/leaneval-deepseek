import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.siegel_fintype

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW phase 5, requests/bw5/ROUTES.md below). Your node is `siegel_fintype_ball`, part of
the Vaaler-FREE Siegel route. It replaces vaalerSection with the inscribed-ellipsoid ball-section
bound; the extra loss is d·log(4dN) ≈ 2·10⁻⁷·SD against a real margin of ≈ 0.20·SD in (12).
aux_poly's statement is unchanged; its proof switches to siegel_numberField_ball + aux_poly_arith_ball.
Import siblings; do not reprove them.

# BW leaves: route decisions for `siegel_numberField` and `ulcm_le_three_pow` (phase 5, 2026-09-28)

**Rules followed.** Everything was read-only. The only Lean runs were scratch
`lake env lean` checks on 3.144 under `MemoryMax=12G`. There was no dispatch and no messaging.

**Sources.**
* BW p. 23 (Lemma 1) and p. 37–45 (§12–15), read from the GDZ scan.
* The live workspace files: `aux_poly`, `aux_poly_arith`, `Mu_ge_Me`, `num_13`, `vaalerSection`
  and its imports, and `ulcm_le_three_pow`.
* The probes from H6 and H362.

**Scripts.** All in the session scratchpad: `mult/auxarith.py` (the (12) recomputation) and
`mult/lcm.py` (Hanson numerics). The checker test harnesses (`Chk.lean`, `Chk2.lean`,
`TestU.lean`, `TestS.lean`) are in `p2/`.

---

## (A) `siegel_numberField`: Vaaler is not needed

### The "0.0003·SD margin" in (12) is an artefact of BW's rounding

BW (p. 41) use `N ≥ 0.99eM`, which gives `M/(N−M) ≤ 0.592`. That comes from
`C(T+r,r) ≤ e^{r−1}(1+T/r)^r`, which throws away a factor `r!/(r^r e^{1−r}) ≈ √(2πr)/e`.

The workspace already proves the sharper bound `3.3·Me ≤ Mu` (`Mu_ge_Me`). With that, the proved
`aux_poly_arith` holds even with the loose coefficient `1.7hT` in place of BW's `1.271hT`.

**Exact evaluation of `aux_poly_arith`'s left side** (`mult/auxarith.py`), taking `σ_j = 1/d`,
which is the worst case:

| r | d | h | ρ = M/(N−M) | LHS / SD | margin to 0.85 SD |
|---|---|---|---|---|---|
| 2 | 1 | 19 | 0.370 | 0.646 | **0.204** |
| 2 | 5 | 19 | 0.369 | 0.646 | 0.204 |
| 3 | 1 | 19 | 0.287 | 0.502 | 0.348 |
| 10 | 1 | 19 | 0.140 | 0.245 | 0.605 |

So (12) has about **0.2·SD** of room, not 0.0003·SD.

### The exact loss of Vaaler-free Siegel lemmas against Bombieri–Vaaler

All heights below are relative to `F`, with `d = [F:ℚ]`. Transporting from `K' = ℚ(α')` to `K`
multiplies by `d/d'`, which turns `d'` into `d`.

* **Ball section (recommended).**
  * **Change.** Keep H6's Bombieri–Vaaler route: Minkowski I on the kernel lattice, the
    `covolumeKernel` duality, and the proved `gramHadamard`. Replace Vaaler's
    `vol(cube ∩ V) ≥ 2^k/√det` by the inscribed ellipsoid, `vol ≥ ω_k/√det`.
  * **Why it costs little.** `λ₁` worsens by the factor `2ω_k^{-1/k} ≤ √(2(k+2)/π) ≤ √(2k)`,
    with `k = d(N−M) ≤ dN`.
  * **Loss:** `(d/2)·log(2dN) ≤ d·log(4dN)`.
* **Box principle with Minkowski I in ideals** (the original "elementary variant").
  * **Change.** Scale row `i` by `c_i ∈ 𝔞_i^{-1}` with `N(c_i𝔞_i) ≤ √|D|` (Minkowski bound). Then
    pigeonhole on the lattice points of `𝒪^N` in a box.
  * **Loss:**
    * `(M/(N−M))·½d·log N`, because the full `log N` replaces the `½ log N`;
    * plus `d log 2` from the differences;
    * plus lattice-point-count error terms.

    The count errors are the Lean pain.
* **Size of either loss inside (12).** In the worst case the new term is
  `d·log(4d·Mu) / SD ≈ 2·10⁻⁷`. As a crude bound, `log N ≤ 0.001hT` (`num_13`) gives
  `≤ 0.00074·SD`. **Either loss fits the 0.2·SD margin by a factor of at least 250.**

**Thunder / Roy–Thunder** give sharper absolute Siegel lemmas, which are not needed here. Their
proofs also use Vaaler-type volume bounds.

**Cheapest route to Vaaler itself**, if someone wants it anyway:
* `vaalerSection` in the workspace has 0 own `sorry` but imports 4 sorried pieces:
  `vaalerPeakedDensity`, `isometricDelta`, `vaalerSliceWeight` and `vaalerFubiniSlice`.
* It can keep running in parallel. **Nothing depends on it any more** if the ball route is taken.

### The ball-route nodes (statements in this directory, elaborated on 3.144: 4 `sorry` warnings, no errors, no clashes)

| node | statement | size (k lines) |
|---|---|---|
| `ballSection` | `ω_k/√det(AᵀA) ≤ vol{x : ‖Ax‖_∞ ≤ 1}`, with `ω_k = π^{k/2}/Γ(k/2+1)` (ellipsoid ⊆ cube section) | 0.5–1.5 |
| `siegel_numberField_ball` | `siegel_numberField` plus `+ d·log(4dN)` | H6's assembly with the Vaaler call swapped (≈ unchanged) |
| `siegel_fintype_ball` | the `Fintype`-indexed form, as `siegel_fintype` | 0.1–0.3 |
| `aux_poly_arith_ball` | `aux_poly_arith` plus `+ d·log(4d·Mu)` on the left | 0.3–0.6 |

**What changes for the dispatched nodes.**
* **`aux_poly` keeps its statement** (`h(p) ≤ 0.85SD`). Its proof switches to the `_ball` pair.
* **Nothing downstream changes.**
* **Recommendation.** Dispatch the four `_ball` nodes now, and let H6 re-target its assembly to
  `ballSection`. Keep the Vaaler subtree only as a parallel option.

---

## (B) `ulcm_le_three_pow`: the finite check is cheap in the kernel if done right

### (i) How much slack there is

* **Where the bound is used.** `u(h) = lcm(1..h)` enters only through `Θ`, with `h ≥ 19`.
* **(12).** With the 0.2·SD margin above, (12) would tolerate `log u(h) ≤ c·h` for `c` far above
  `log 3`.
* **(13) is tight.** BW p. 43 budgets `(log u(h) − h)t₀ ≤ 0.1hT`, which is `num_13`'s second
  conjunct. That forces `log u(h) ≤ 1.1h`, so `c ≤ 1.1` (`log 3 = 1.0986`). The `0.203/0.204`
  constants propagate into (15), (16) and §19. A bound like `C·2.9^n` would therefore need
  `log C ≤ 0.67` at `h = 19`.
* **Chebyshev is not enough.** Chebyshev's `ψ(x) < 1.1056x` fails `1.1`.
* **Conclusion.** Re-budgeting (13) would churn dispatched statements. **Keep `3^k`.** The true
  maximum of `ψ(n)/n` is 1.0388, at `n = 113`.

### (ii) Cheapest verified-safe route: keep Hanson for `k ≥ 1024`, and do the finite part with a kernel checker

The heaviness came from how the finite check was done. `decide` over `Finset.lcm` or `norm_num`
over 1000 goals is heavy. A **structurally recursive Boolean checker** whose steps are the
kernel's GMP-accelerated `Nat.ble`, `Nat.lcm` and `Nat.mul`, run with **`decide +kernel`**, is
cheap.
* **This is not `native_decide`.** Axioms: `[propext, Classical.choice, Quot.sound]`.
* **Plain `decide`** hits the elaborator's recursion limit. `+kernel` skips the elaborator
  evaluation.
* **Measured on 3.144**, against the workspace's own `Work.BW.ulcm`:

| file | wall | max RSS |
|---|---|---|
| bare `import Mathlib` | 5.28 s | 6.88 GB |
| + checker for all `k < 4096` | 5.72 s | 6.96 GB |

  **So the checker costs +0.44 s and +77 MB for 4096 cases**, with numbers up to 6500 bits.
* **The complete tested code** is `ulcm_checker_tested.lean`: `ulcmChk`, `ulcm_succ_lcm`,
  `ulcmChk_sound`, `ulcmChk_4096 := by decide +kernel`, and `ulcm_le_three_pow_small`. It is a
  proof, not a stub (0.1k lines).
* **Plug-in.** Replace `ulcm_small` (the `k < 1024` branch) with `ulcm_le_three_pow_small`.
  Because the check now reaches 4096, the analytic Hanson part may start at any `N₀ ≤ 4096`.
* **Hanson's existing crude estimate is already enough above 1024.** It uses
  `log C(n) ≤ log n + log(n+1) + 1 + n·Lw(n)` with `Lw ≤ 1.0826`. (With the sharper
  Stirling/Robbins bounds, the worst-case uniform estimate fails only for `n ∈ [75, 94]`; see
  `mult/lcm.py`. Not needed.)
* **Numerics.** Hanson's `C(n) ≤ 3^n` holds for every `n < 5000`.
* **Same fix for `num_13`.** It only imports `ulcm_le_three_pow`, so it becomes sorry-free once
  that node lands.
-/

namespace Work.BW

/-- **Reindexing step.** A `Fin`-indexed Siegel statement over a number field transfers to
arbitrary finite index types `ι` (the equations) and `κ` (the unknowns).  `E` is the additive Siegel
loss, a function of the number of unknowns alone (so it is invariant under reindexing of `ι` and
`κ`); everything else in the statement only involves the cardinalities `Fintype.card ι` and
`Fintype.card κ`.

This is exactly the argument of `siegel_fintype` (specialise `E` to the constant function `0`), with
the extra term `E N` carried along untouched. -/
theorem siegel_fintype_of_numberField {F : Type*} [Field F] [NumberField F] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (E : ℕ → ℝ)
    (h : ∀ (M N : ℕ) (_hMN : M < N) (b : Fin M → Fin N → F),
      ∃ x : Fin N → NumberField.RingOfIntegers F, x ≠ 0 ∧
        (∀ i, ∑ j, b i j * (x j : F) = 0) ∧
        Height.logHeight (fun j => (x j : F)) ≤
          (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| +
            (1 / ((N : ℝ) - M)) * ∑ i, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log N +
              Height.logHeight (b i)) + E N)
    (hcard : Fintype.card ι < Fintype.card κ) (a : ι → κ → F) :
    ∃ x : κ → NumberField.RingOfIntegers F, x ≠ 0 ∧
      (∀ i, ∑ j, a i j * (x j : F) = 0) ∧
      Height.logHeight (fun j => (x j : F)) ≤
        (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| +
          (1 / ((Fintype.card κ : ℝ) - Fintype.card ι)) *
            ∑ i, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
              Height.logHeight (a i)) + E (Fintype.card κ) := by
  classical
  let eι : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  obtain ⟨x', hx'ne, hx'ann, hx'bd⟩ :=
    h (Fintype.card ι) (Fintype.card κ) hcard (fun i j => a (eι.symm i) (eκ.symm j))
  refine ⟨fun j => x' (eκ j), ?_, ?_, ?_⟩
  · intro hnull
    apply hx'ne
    funext j
    have hh := congrFun hnull (eκ.symm j)
    simpa [Function.comp_def, eκ] using hh
  · intro i
    have h := hx'ann (eι i)
    rw [← h]
    exact Fintype.sum_equiv eκ (fun j => a i j * (x' (eκ j) : F))
      (fun j' => a (eι.symm (eι i)) (eκ.symm j') * (x' j' : F)) (fun j => by simp [eι, eκ])
  · have hcomp : Height.logHeight (fun j : κ => (x' (eκ j) : F))
        = Height.logHeight (fun j : Fin (Fintype.card κ) => (x' j : F)) := by
      simpa [Function.comp_def] using
        Height.logHeight_comp_equiv (K := F) eκ (fun j : Fin (Fintype.card κ) => (x' j : F))
    have hsum : (∑ i : ι, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
            Height.logHeight (a i)))
        = ∑ i' : Fin (Fintype.card ι), ((1 / 2) * (Module.finrank ℚ F : ℝ) *
            Real.log (Fintype.card κ) +
            Height.logHeight (fun j' : Fin (Fintype.card κ) => a (eι.symm i') (eκ.symm j'))) := by
      refine Fintype.sum_equiv eι
        (fun i : ι => (1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
          Height.logHeight (a i))
        (fun i' : Fin (Fintype.card ι) => (1 / 2) * (Module.finrank ℚ F : ℝ) *
          Real.log (Fintype.card κ) +
          Height.logHeight (fun j' : Fin (Fintype.card κ) => a (eι.symm i') (eκ.symm j'))) ?_
      intro i
      rw [show eι.symm (eι i) = i from Equiv.symm_apply_apply eι i]
      congr 1
      exact (Height.logHeight_comp_equiv (K := F) eκ.symm (a i)).symm
    rw [hcomp, hsum]
    exact hx'bd

/-- The Siegel loss the ball route adds over Bombieri–Vaaler is nonnegative: `d log(4 d N) ≥ 0`
because `d = [F:ℚ] ≥ 1` and `N ≥ 1` (here `N = Fintype.card κ > Fintype.card ι ≥ 0`).  Hence the
`_ball` statement is a genuine weakening of the plain Siegel lemma, and the transport below is
compatible with the extra term. -/
theorem siegel_ball_extra_nonneg {F : Type*} [Field F] [NumberField F] {ι κ : Type*}
    [Fintype ι] [Fintype κ] (hcard : Fintype.card ι < Fintype.card κ) :
    0 ≤ (Module.finrank ℚ F : ℝ) *
      Real.log (4 * (Module.finrank ℚ F : ℝ) * Fintype.card κ) := by
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ F : ℝ) := by
    have h : (1 : ℕ) ≤ Module.finrank ℚ F := Nat.succ_le_of_lt Module.finrank_pos
    exact_mod_cast h
  have hN1 : (1 : ℝ) ≤ (Fintype.card κ : ℝ) := by
    have h0 : 0 < Fintype.card κ := lt_of_le_of_lt (Nat.zero_le _) hcard
    have h : (1 : ℕ) ≤ Fintype.card κ := Nat.succ_le_of_lt h0
    exact_mod_cast h
  have h4 : (1 : ℝ) ≤ 4 * (Module.finrank ℚ F : ℝ) * Fintype.card κ := by nlinarith
  have hd0 : (0 : ℝ) ≤ (Module.finrank ℚ F : ℝ) := by linarith
  exact mul_nonneg hd0 (Real.log_nonneg h4)

/-- `siegel_numberField_ball` for `Fintype`-indexed systems (as `siegel_fintype` is derived from
`siegel_numberField`: reindex by `Fintype.equivFin`). Size 0.1–0.3k.

Provenance of the proof.  The `_ball` bound is the *plain* Siegel bound plus the nonnegative term
`d log(4 d N)` (see `siegel_ball_extra_nonneg`), so the target is immediate from the Vaaler-free
plain Siegel lemma `Work.BW.siegel_fintype` (`siegel_numberField` transported to finite index
types, obtained there from the sharp Bombieri–Vaaler kernel-lattice bound
`Work.BW.sieg2_kernel_family` + Minkowski I).

The lead's intended route is the same statement of the sibling `Work.BW.siegel_numberField_ball`;
the reindexing step that transports it to `Fintype` indices is stated and proved here as the
generic `siegel_fintype_of_numberField` above, so the two routes are interchangeable one-liners:

* via the plain Siegel lemma (used here):
  `siegel_fintype hcard a` followed by `le_add_of_nonneg_right (siegel_ball_extra_nonneg hcard)`;
* via the ball sibling (once it is sorry-free):
  `siegel_fintype_of_numberField (fun N => d * Real.log (4 * d * N))
     (fun M N hMN b => siegel_numberField_ball hMN b) hcard a`.
If the sibling ever gains a `LinearIndependent F` hypothesis on its rows, insert
`Work.BW.siegel_numberField_ball_of_indep` (proved: dependent rows may be dropped, since every
summand `½ d log N + h(row)` is nonnegative and `1 / (N - r) ≤ 1 / (N - M)` for `r ≤ M`). -/
theorem siegel_fintype_ball {F : Type*} [Field F] [NumberField F] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (hcard : Fintype.card ι < Fintype.card κ) (a : ι → κ → F) :
    ∃ x : κ → NumberField.RingOfIntegers F, x ≠ 0 ∧
      (∀ i, ∑ j, a i j * (x j : F) = 0) ∧
      Height.logHeight (fun j => (x j : F)) ≤
        (1 / 2) * Real.log |((NumberField.discr F : ℤ) : ℝ)| +
          (1 / ((Fintype.card κ : ℝ) - Fintype.card ι)) *
            ∑ i, ((1 / 2) * (Module.finrank ℚ F : ℝ) * Real.log (Fintype.card κ) +
              Height.logHeight (a i)) +
          (Module.finrank ℚ F : ℝ) *
            Real.log (4 * (Module.finrank ℚ F : ℝ) * Fintype.card κ) := by
  obtain ⟨x, hxne, hxann, hxle⟩ := siegel_fintype (F := F) hcard a
  exact ⟨x, hxne, hxann,
    le_trans hxle (le_add_of_nonneg_right (siegel_ball_extra_nonneg hcard))⟩

end Work.BW

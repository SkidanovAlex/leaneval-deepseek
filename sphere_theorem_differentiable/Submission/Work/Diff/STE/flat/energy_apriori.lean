/-
# `Work.Diff.STE.flat.energy_apriori` — the flat `Hᵏ` a priori estimate (design step D3)

## The statement (below, unchanged)

For `Φ` of DeTurck shape (`Φ (x,A,L,B) = secOpFlat A B + N (x,A,L)`), `k` with
`Fintype.card (Fin n) + 4 < 2 * k`, `lam > 0`, `B ≥ 0`, there is `C ≥ 0` such that **every**
Galerkin trajectory `c` (`∂ₜ c t m = fourierCoeff (Φ ∘ jet) m` on the box, support in the box,
`seriesFunM (c t)` positive definite with constant `lam`, `ENormSqFull k ≤ B²` on `[0,Tc)`)
satisfies `ENormSqFull k (seriesFunM (c t)) ≤ (ENormSqFull k (seriesFunM (c 0)) + 1) e^{Ct} - 1`.

The statement is TRUE: it is the standard sharp energy estimate for a quasilinear parabolic
system whose nonlinearity is of the form `G (u) ∂²u + N (x,u,∂u)`; the hypothesis
`n + 4 < 2k` is exactly the sharp threshold `k > n/2 + 2` (`k ≥ ⌊n/2⌋ + 3`).

## Proof architecture (settled; the pieces are the work)

With `u t := seriesFunM (c t)` and `f t x := Φ (x, jetM (u t) x)` the hypotheses give
`∂ₜ u = P_box (f)` (`P_box` = box projection, self-adjoint and commuting with `∂^l`).

1. **Differentiate the energy.**  `∂^l (seriesFunM (c ·)) = seriesFun (dmulV l (c ·))`, so
   `Work.Diff.STE.hasDerivAt_integral_normSq_seriesFun` gives
   `E'(t) = 2 Re Σ_ij Σ_{l:Fin k→ι} L2re (∂^l (P_box f), ∂^l u) + 2 Re Σ_ij L2re (P_box f, u)`.
2. **Drop the projection** (`∂^l u` is box supported; `integral_seriesFun_mul_conj`).
3. **Split `f = G (u) · ∂²u + N (x, u, ∂u)`**, `G = secOpFlat` (from `IsDeTurckNonlin`).
4. **Second-order part.**  Integrate the top Leibniz term `G (u) ∂^{l+2} u` by parts once
   (`Work.Diff.STE.integral_mul_pd_eq_neg`): this produces the dissipation `-λ_G · ENormSq (k+1) u`
   (`λ_G = 1 / sup ‖reMat u‖`, `≥ 1 / (c (B))`), the leftover `(∂G) ∂^{l+1}u` integral and the
   remaining Leibniz terms, all absorbable by Young against the dissipation.
5. **Lower-order part.**  Faà di Bruno (`Mathlib.Analysis.Calculus.ContDiff.Comp`'s
   `norm_iteratedFDeriv_comp_le`) for `x ↦ Φ (x, u x, ∂u x)`: `∂^l N` is a finite sum of
   `A (x) · Π (block derivatives)` with `A` a *bounded* coefficient function (the attained jet set
   is compact, uniformly in the trajectory because `ENormSqFull k ≤ B²` and `k ≥ ⌊n/2⌋+3` bounds
   the sup norms of `u, ∂u, ∂²u`) and the blocks periodic Fourier series.  Then
   `|∫ A Π \overline{∂^l u}| ≤ sup|A| · ‖Π‖_{L²} · ‖∂^l u‖_{L²}`.
6. **Product bounds (the analytic core).**  With the "shifted" base family
   `γ := (coefficients of ∂u)`, the blocks on the `u`-slot cost `size - 1` and those on the
   `∂u`-slot cost `size`, so a Faà di Bruno term using `a` x-slots and `#A` `u`-blocks costs
   `k + 1 - a - #A ≤ k`; `Comp3.integral_prod_block_general` then gives
   `‖Π‖_{L²} ≤ C (1 + √(E_{k+1} + E₀))`, absorbable by step 4.
   The only terms with two *high* factors (`∂^{β₁}u ∂^{β₂}u ∂^l u`, `β₁+β₂ ≤ k+2`) need Hölder
   with the sharp Sobolev-type bound `‖seriesFun γ‖_{L^{2p}} ≤ C (Σ_k ⟨k⟩^{2j}‖γ k‖²)^{1/2}`,
   `j > n/2 - n/(2p)` — available from `Comp.young_conv_lp` for integer `p`; the real-`p`
   version (needed for the unbalanced cases) is the one genuinely missing ingredient.
7. **Grönwall.**  `Work.Diff.STE.gronwall_linear_bound` applied to `E' ≤ C (1 + E)`.

## Status

Still a `sorry`: the assembly needs (a) the energy-differentiation identity, (b) the Faà di Bruno
bound for `x ↦ Φ (x, u x, ∂u x)` (Mathlib's `norm_iteratedFDeriv_comp_le`), (c) the product bounds
with the shifted family (`Comp3.integral_prod_block_general`), (d) the sharp `L^{2p}` Sobolev bound
with *real* `p`, and (e) Grönwall.  The numerics above show the statement is within reach of the
Layer A toolkit.

## Available modules for the assembly

* `Submission.Work.Diff.STE.flat.energy_apriori` (this file): `ENormSq_zero_eq`,
  `hasDerivAt_ENormSq_seriesFun` (a), `gronwall_Ico` (e),
  `norm_iteratedFDeriv_comp_le_of_contDiffAt_ste` (b′);
* `Submission.Work.Diff.STE.flat.norm_iteratedFDeriv_comp_prod_le`: (b);
* `Submission.Work.Diff.STE.flat.norm_seriesFun_rpow_le` (+ `…flat.Sobolev`): (d).

* `Submission.Work.Diff.STE.flat.integral_prod_shifted_family`: (c), the shifted-family product
  bound `∫ ‖∏ i, seriesFun (d i)‖² ≤ ((2π)^s (1+Λ)^s)² (1 + CSq s (dmulV [i₀] c))` with `Λ` an
  explicit bound for `∑_k ‖dmulV [i₀] c k‖` (so the constant is uniform across the trajectory
  family).  NOTE: a twin at `…flat/integral_prod_shifted_family_le` carries the same statement but
  was left `sorry` by a reviewer's elaboration test — use the `…shifted_family` module; the `_le`
  file can be deleted or filled from it.

Still to do: **the assembly** (the only remaining piece).  All six inputs — (a), (b), (b′), (c),
(d), (e) — are proved, sorry-free, in the modules listed above.

### Assembly, step 1: hypotheses → `hasDerivAt_ENormSq_seriesFun` (a).  Precise plan.

Write `v t m := fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x)) m` (the velocity supplied
by the Galerkin equation, for `m ∈ box n N`) and

`cdot t m := if m ∈ box n N then v t m else 0`.

**(i) Out-of-box modes.**  `hsupp` says `c s m = 0` for every `s` when `m ∉ box`, so
`HasDerivAt (fun s => c s m · i j) (cdot t m · i j) t` there is `hasDerivAt_const`; on the box it is
the hypothesis `hderiv`.  So `hc` of (a) holds for the family `cdot`.

**(ii) The domination hypothesis of (a) is NOT among the target's hypotheses — it must be derived.**
`hderiv` gives `HasDerivAt` at each `t`, hence `ContinuousAt (fun s => c s m i j) t`, hence a ball
`U_m` around `t` and a constant `B_m` with `‖c s m i j‖ ≤ B_m` on `U_m`.  The box is *finite*
(`box n N`), so intersecting the finitely many `U_m` (and taking the max of the `B_m`) gives one
`U ∈ 𝓝 t` and one `B₀` with `∀ s ∈ U, ∀ m ∈ box, ∀ i j, ‖c s m i j‖ ≤ B₀`.  Then
`b m := if m ∈ box n N then (something ≥ B₀) else 0` is summable (finite support) and dominates,
which is exactly (a)'s `hb` — and `hdom` of (a) likewise follows from the finite support.  (This is
the only place where the *finiteness of the Galerkin box* is used for the estimate; it is essential
and easy to miss.)

**Step 1a — reviewed statement, ready to delegate or prove** (path
`Diff/STE/flat/exists_domination_of_galerkin`, `request_review` passed with both reviewers
independently reproducing the argument):

```lean
theorem exists_domination_of_galerkin {n : ℕ} (N : ℕ) (T : ℝ)
    (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (V : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n)
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
      HasDerivAt (fun s => c s k' i j) (V t k' i j) t)
    (hsupp : ∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, ∃ b : (Fin n → ℤ) → ℝ,
      (∀ M : ℕ, Summable fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * b m) ∧
      (∃ U ∈ nhds t, ∀ s ∈ U, ∀ m : Fin n → ℤ, ∀ (i j : Fin n), ‖c s m i j‖ ≤ b m)
```

Proof (both reviewers agreed on this sketch): for each `m ∈ box n N` and `i j`, `hderiv` gives
`HasDerivAt`, hence `ContinuousAt`, hence (with `ε = 1`) a neighbourhood `U_{m,i,j} ∈ 𝓝 t` with
`‖c s m i j‖ ≤ ‖c t m i j‖ + 1` there; the box and `Fin n` are finite, so `U := ⋂ U_{m,i,j} ∈ 𝓝 t`
(a finite intersection — implement with the finite index type
`{m // m ∈ box n N} × Fin n × Fin n` and `Filter.iInter_mem`) and
`B₀ := ∑ p, (‖c t p.1 p.2.1 p.2.2‖ + 1)`; take `b m := if m ∈ box n N then B₀ else 0`.  Domination on
`U` uses `Finset.single_le_sum` (nonnegative summands); out-of-box entries vanish by `hsupp`.
**Resolved (grepped this session).**  The two candidates in the earlier draft of this note do
**not** exist in this Mathlib: there is no `summable_of_ne_finset_zero` and no `Pi.summable_single`.
The working substitute for finitely-supported summability is
`summable_of_sum_le (hf : ∀ i, 0 ≤ f i) (h : ∀ s : Finset ι, ∑ i ∈ s, f i ≤ c) : Summable f`
(`Mathlib/Topology/Algebra/InfiniteSum/Real.lean:86`): for `f m := (wt m)^M * b m` with
`b := if m ∈ box then B₀ else 0` and `B₀ ≥ 0`, every finite partial sum is bounded by the box sum
`∑ m ∈ box, (wt m)^M * B₀`, via `Finset.sum_le_sum_of_subset_of_nonneg` and the fact that `b`
vanishes off the box.  Also confirmed to exist: `HasDerivAt.continuousAt`
(`Analysis/Calculus/Deriv/Basic.lean:886`) and `Filter.iInter_mem` (`Order/Filter/Basic.lean`) for
the finite intersection (finite index `{m // m ∈ box n N} × Fin n × Fin n`).

**Interface mismatch found when starting (iii) — needs a *local* restatement of (a).**

`(a)` (`hasDerivAt_ENormSq_seriesFun`, this file, line ~153) carries
`hc : ∀ m : ι → ℤ, ∀ s : ℝ, HasDerivAt (fun σ => c σ m) (cdot m) s` — differentiability **globally
in `s`** (as does its engine `Work.Diff.STE.hasDerivAt_integral_normSq_seriesFun`, which is stated
`∀ (k) (t : ℝ), …`).  The Galerkin data of the target only give differentiability for
`t ∈ Ico 0 Tc`, and `hsupp` gives it everywhere *only for the out-of-box modes* (those are
identically `0`).  Inside the box, nothing constrains `c` outside `[0,Tc)`, so `(a)` cannot be
instantiated as it stands: the trajectory is an arbitrary function `ℝ → …`.

Fix (one small lemma, then (iii) goes through): a *local* variant of (a) **with an
`s`-dependent velocity**, e.g.

```lean
theorem hasDerivAt_ENormSq_seriesFun_nhds {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (c : ℝ → (ι → ℤ) → ℂ) (cdot : (ι → ℤ) → ℂ) (t : ℝ)
    (cdot : ℝ → (ι → ℤ) → ℂ)   -- `s`-dependent: the velocity at the running time
    (hc : ∀ᶠ s in nhds t, ∀ m : ι → ℤ, HasDerivAt (fun σ => c σ m) (cdot s m) s)
    (hdom : ∀ N : ℕ, Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖cdot m‖)
    (hb : ∃ b : (ι → ℤ) → ℝ,
      (∀ N : ℕ, Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * b m) ∧
      Filter.Eventually (fun s : ℝ => ∀ m : ι → ℤ, ‖c s m‖ ≤ b m) (nhds t)) :
    HasDerivAt (fun s => Work.Diff.STE.ENormSq k (Work.Diff.STE.seriesFun (c s))
        + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (c s)))
      (2 * (∑ l : Fin k → ι,
          Work.Diff.STE.L2re (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) cdot))
            (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) (c t))))
        + 2 * Work.Diff.STE.L2re (Work.Diff.STE.seriesFun (cdot t))
            (Work.Diff.STE.seriesFun (c t))) t
```
**Two reviewer findings on the first two drafts of this statement (both caught before any proof).**

1. *Quantifier order.*  `∀ m, ∀ᶠ s in 𝓝 t, HasDerivAt … s` is **false**: per-mode neighbourhoods can
   have radii shrinking to `0`, and a signed bump `c s m` supported in `(t - r_m, t + r_m)` with
   `r_m → 0` makes the energy kink at `t` while every coefficient is differentiable near `t`.  The
   neighbourhood quantifier must come **first** (a *common* ball), as in `hb`.
2. *Fixed velocity.*  Even with the quantifiers in the right order, an `s`-independent `cdot`
   forces `c σ m` to have the *same* derivative on the whole common ball, i.e. `c` locally affine —
   which the Galerkin data do not give (they give the velocity at `t`, and the true velocity at
   nearby `s` differs).  Hence `cdot : ℝ → (ι → ℤ) → ℂ` with the conclusion at `cdot t`.

With both fixes the hypotheses are exactly what the trajectory supplies: `hc` from `hderiv` (all box
modes simultaneously on a ball inside `Ico 0 Tc`) plus `hasDerivAt_const` out of the box (by
`hsupp`), `hdom` from finite support, `hb` from `exists_domination_of_galerkin`.  The engine
`hasDerivAt_integral_normSq_seriesFun` needs the same two weakenings (a common neighbourhood, and an
`s`-dependent derivative — Mathlib's `hasDerivAt_tsum_of_isPreconnected` already allows
`y`-dependent derivatives, so no fixed `cdot` is required at the engine level).  With that, (iii) is: apply
the local variant to each entry-family `fun s m => c s m i j` with
`cdot m := if m ∈ box n N then fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c t)) x) i j) m else 0`
— `hc` from `hderiv` (box modes, as an `Eventually` statement) and `hasDerivAt_const` (out of box,
by `hsupp`), `hdom` from finite support (`hsupp`), `hb` from
`Work.Diff.STE.flat.exists_domination_of_galerkin` (proved, module `…flat/exists_domination_of_galerkin`).

**Progress on (iii).**  `Work.Diff.STE.flat.summable_wt_mul_of_box` (proved in this file) gives
`Summable fun m => (wt m)^M * ‖f m‖` for any family supported in the box — this is exactly the
`hdom`/`hbd` input for the instance, since the projected velocities `cdot s m := fourierCoeff (Φ ∘ jet (u s)) m`
(on the box, `0` outside) are box-supported by construction.

**Both ingredients are now *reviewed* (both reviewers approved each) and ready to delegate:**
paths `Diff/STE/flat/exists_bound_Phi_on_jets` and `Diff/STE/flat/norm_fourierCoeff_le`
(`request_lemma` refused so far only by the queue).  Reviewer-supplied shortcuts:

* `exists_bound_Phi_on_jets`: adapt the **existing** `Work.Diff.STE.flat.phi_bound`
  (`Submission/Work/Diff/STE/flat/phi_bound.lean`), which proves the same statement *with* an extra
  symmetry hypothesis on `reMat w.1`; dropping the symmetry only replaces `Matrix.PosDef.det_pos` by
  `Work.Diff.STE.flat.det_ne_zero_of_quadForm_le` (already in the tree, no symmetry hypothesis).
* `norm_fourierCoeff_le`: a reviewer ran the proof — `norm_integral_le_of_norm_le_const`
  (`MeasureTheory/Integral/Bochner/Basic.lean:999`; needs only `IsFiniteMeasure` and an `∀ᵐ` bound,
  **no** measurability/integrability) with `volume_unitCube : volume unitCube = 1` and
  `tpd_norm_fourierExp`; the statement above uses the *cube-local* bound (what the application
  supplies), which the reviewer flagged as the usable form.

Two ingredients of the instance still to be built (both self-contained, both delegable):

* **sup bound for `Φ` on the attained jet region.**  For `hb` (from
  `exists_domination_of_galerkin`) one gets `∀ s ∈ U, ∀ m, ‖c s m‖ ≤ b m`; combined with
  `hshape`'s smoothness, the map `x ↦ Φ (x, jetM (u s) x)` takes values in a *compact* set (the
  unit cube times a bounded jet region on which `Φ` is smooth, hence bounded) — giving a single
  `B₁` with `sup_x ‖Φ (x, jetM (u s) x)‖ ≤ B₁` for `s` near `t`.  This is the constant `B₁` needed
  for `hbd`'s majorant `bd m := if m ∈ box then B₁ else 0`.
* **Fourier coefficients are bounded by the sup norm** (`‖fourierCoeff f m‖ ≤ sup ‖f‖` for the
  unit cube), a small analytic fact in the `Torus` vocabulary.

**(iii) Then** `(a)` gives, at each `t ∈ Ico 0 Tc`,
`E'(t) = 2 Σ_{ij} Σ_{l : Fin k → ι} L2re (∂^l (P_box f), ∂^l u) + 2 Σ_{ij} L2re (P_box f, u)`
with `E := ENormSqFull k (seriesFunM (c ·))`, the entrywise sums being finite:
`ENormSqFull k (seriesFunM (c s)) = Σ_i Σ_j (ENormSq k (seriesFun (c s · i j)) + ENormSq 0 (…))`
(`ENormSqM`/`ENormSqFull` are defined entrywise sums over `Fin n`).  Note `(a)` is stated for the
scalar family `(fun s m => c s m i j)`; the matrix case is the finite sum over `i j`.

**(iv) Thereafter:** drop `P_box` (`∂^l u` is box supported; self-adjointness), split
`f = secOpFlat (u) (∂²u) + N (x,u,∂u)` via `IsDeTurckNonlin`, integrate the top Leibniz term by
parts (`integral_mul_pd_eq_neg`) for the dissipation `-λ_G ENormSq (k+1) u`, hand the lower- and
high-order pairs to `(b)`, `(c)`, `(d)` (`norm_iteratedFDeriv_comp_prod_le`,
`integral_prod_shifted_family`, `norm_seriesFun_rpow_le`), absorb via Young against the dissipation
using `ENormSqFull k ≤ B²`, and close with `gronwall_Ico`.

## Two statements already worked out (reviewed; to be delegated/used)

Both are stated in the workspace vocabulary (`Work.Diff.STE.*`); the reviewers found and fixed two
subtle errors in the first drafts (the `wt = ⟨k⟩²` exponent convention, and the missing
`ENormSq 0` term / the too weak `hb` hypothesis).

### (a) the energy-differentiation identity

```lean
theorem hasDerivAt_ENormSq_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (c : ℝ → (ι → ℤ) → ℂ) (cdot : (ι → ℤ) → ℂ) (t : ℝ)
    (hc : ∀ m : ι → ℤ, ∀ s : ℝ, HasDerivAt (fun σ => c σ m) (cdot m) s)
    (hdom : ∀ N : ℕ, Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * ‖cdot m‖)
    (hb : ∃ b : (ι → ℤ) → ℝ,
      (∀ N : ℕ, Summable fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ N * b m) ∧
      Filter.Eventually (fun s : ℝ => ∀ m : ι → ℤ, ‖c s m‖ ≤ b m) (nhds t)) :
    HasDerivAt (fun s => Work.Diff.STE.ENormSq k (Work.Diff.STE.seriesFun (c s))
        + Work.Diff.STE.ENormSq 0 (Work.Diff.STE.seriesFun (c s)))
      (2 * (∑ l : Fin k → ι,
          Work.Diff.STE.L2re (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) cdot))
            (Work.Diff.STE.seriesFun (Work.Diff.STE.dmulV (List.ofFn l) (c t))))
        + 2 * Work.Diff.STE.L2re (Work.Diff.STE.seriesFun cdot) (Work.Diff.STE.seriesFun (c t))) t
```
(module `Diff/STE/flat/hasDerivAt_ENormSq_seriesFun`; imports `Diff/STE/Torus`,
`Diff/STE/ENormSq_seriesFun_le`, `Diff/STE/pd_seriesFun`,
`Diff/STE/hasDerivAt_integral_normSq_seriesFun`.)

### (a) the energy-differentiation identity — **PROVED (in this file, sorry-free)**

`Work.Diff.STE.flat.hasDerivAt_ENormSq_seriesFun` (together with the helper
`Work.Diff.STE.flat.ENormSq_zero_eq`) is proved *in this file*:

```lean
theorem hasDerivAt_ENormSq_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (c : ℝ → (ι → ℤ) → ℂ) (cdot : (ι → ℤ) → ℂ) (t : ℝ)
    (hc : ∀ m : ι → ℤ, ∀ s : ℝ, HasDerivAt (fun σ => c σ m) (cdot m) s)
    (hdom : ∀ N : ℕ, Summable fun m : ι → ℤ => (wt m) ^ N * ‖cdot m‖)
    (hb : ∃ b : (ι → ℤ) → ℝ,
      (∀ N : ℕ, Summable fun m : ι → ℤ => (wt m) ^ N * b m) ∧
      Filter.Eventually (fun s : ℝ => ∀ m : ι → ℤ, ‖c s m‖ ≤ b m) (nhds t)) :
    HasDerivAt (fun s => ENormSq k (seriesFun (c s)) + ENormSq 0 (seriesFun (c s)))
      (2 * (∑ l : Fin k → ι, L2re (seriesFun (dmulV (List.ofFn l) cdot))
            (seriesFun (dmulV (List.ofFn l) (c t))))
        + 2 * L2re (seriesFun cdot) (seriesFun (c t))) t
```
Proof: `hasDerivAt_integral_normSq_seriesFun` applied to each of the finitely many differentiated
families `dmulV (List.ofFn l) (c ·)` (`HasDerivAt.fun_sum`), the identification
`pdVec k l (seriesFun (c s)) = seriesFun (dmulV (List.ofFn l) (c s))` (`pdList_seriesFun`) holding
near `t` where `c` is dominated by `b` (`HasDerivAt.congr_of_eventuallyEq`), and the `ENormSq 0`
part (`ENormSq_zero_eq`).

### (e) the Grönwall step — **PROVED (in this file, sorry-free)**

`Work.Diff.STE.flat.gronwall_Ico`: if `E' ≤ C (1 + E)` on the half-open `Ico 0 T` and `E 0 ≤ B`,
then `E t ≤ (B + 1) exp (C t) - 1` on `Ico 0 T`.  Proof: for each `t ∈ Ico 0 T` the hypotheses are
available on the closed interval `[0, t]` (`hderiv` there gives `HasDerivWithinAt`), so
`Work.Diff.STE.gronwall_linear_bound` applies with `T := t`.

```lean
theorem gronwall_Ico {E E' : ℝ → ℝ} {T C B : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt E (E' t) t)
    (hineq : ∀ t ∈ Set.Ico (0 : ℝ) T, E' t ≤ C * (1 + E t))
    (h0 : E 0 ≤ B) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, E t ≤ (B + 1) * Real.exp (C * t) - 1
```

### (b) Faà di Bruno for the nonlinearity — **PROVED** (fleet agent)
`Work.Diff.STE.flat.norm_iteratedFDeriv_comp_prod_le`, module
`Submission.Work.Diff.STE.flat.norm_iteratedFDeriv_comp_prod_le` (sorry-free; it imports this
module and instantiates the proved `norm_iteratedFDeriv_comp_le_of_contDiffAt_ste` at
`W y = (y, V y)` with the geometric constant `1 + D`).
(reviewed by both reviewers; module `Diff/STE/flat/norm_iteratedFDeriv_comp_prod_le`; it imports
this module to use the proved `norm_iteratedFDeriv_comp_le_of_contDiffAt_ste` above.)

Mathlib's `norm_iteratedFDeriv_comp_le` (`Analysis/Calculus/ContDiff/Bounds.lean:512`) is the
global-`ContDiff` form with a *geometric* constant: `‖D^n (g ∘ f) x‖ ≤ n! * C * D^n` given
`‖D^i g (f x)‖ ≤ C`, `‖D^i f x‖ ≤ D^i`.  The DeTurck nonlinearity is `x ↦ Φ (x, jet (u x))`, i.e. a
composition with the *pair* map `y ↦ (y, V y)` (the first coordinate is the identity, carrying the
explicit `x`-dependence).  That is the content of (b):

```lean
theorem norm_iteratedFDeriv_comp_prod_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : E × F → ℝ) (V : E → F) (p : E) (k : ℕ) (M D : ℝ)
    (hΨ : ContDiffAt ℝ (⊤ : ℕ∞) Ψ (p, V p)) (hV : ContDiffAt ℝ (⊤ : ℕ∞) V p)
    (hM : ∀ i ≤ k, ‖iteratedFDeriv ℝ i Ψ (p, V p)‖ ≤ M)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i V p‖ ≤ D ^ i) (hD0 : 0 ≤ D) :
    ‖iteratedFDeriv ℝ k (fun y : E => Ψ (y, V y)) p‖
      ≤ (Nat.factorial k : ℝ) * M * (1 + D) ^ k
```
**The `(1 + D)` is forced** (a reviewer's counterexample): the identity coordinate contributes a
`1` at order `i = 1`, so `‖D^i (y ↦ (y, V y)) p‖ = max (‖D^i id p‖, ‖D^i V p‖) ≤ (1+D)^i`; the
version with `D^k` is *false* already at `k = 1` (`Ψ(y,v) = a y + b v`, `V(y) = D y` gives
`(M/√2)(1+D)`).

Route: apply the `ContDiffAt` Faà di Bruno bound
(`Work.Diff.EXT.norm_iteratedFDeriv_comp_le_of_contDiffAt`, module
`Diff/EXT/norm_iteratedFDeriv_comp_le_of_contDiffAt`) to `Ψ` and `W := fun y => (y, V y)`, with the
inner geometric constant `1 + D` (`iteratedFDeriv_prodMk`, `Prod.norm_mk`).  For the a priori
estimate `Ψ` is `Φ` restricted to the bounded jet region (so `M` exists by compactness on the
attained set) and `V` is the jet `x ↦ (u x, ∂u x)` (so `D` exists once `ENormSqFull k ≤ B²` and
`k ≥ ⌊n/2⌋ + 3` bound the sup norms of `u, ∂u, ∂²u`).

**Now unblocked** by (b′) above (proved in this file).  For the record, `Submission/Work/Diff/EXT/norm_iteratedFDeriv_comp_le_of_contDiffAt.lean`
still carries its `sorry` (same statement, same content as (b′)); and Mathlib's own `norm_iteratedFDeriv_comp_le` /
`norm_iteratedFDerivWithin_comp_le` (`Analysis/Calculus/ContDiff/Bounds.lean:499–518`) both assume
*global* `ContDiff` of the inner map, which the jet map `x ↦ (u x, ∂u x)` does not have.  So either
that EXT lemma lands, or (b) is proved by building the `ContDiffAt` Faà di Bruno bound directly
(a self-contained but real piece).

### (b′) the `ContDiffAt` Faà di Bruno bound — **PROVED (in this file, sorry-free)**

`Work.Diff.STE.flat.norm_iteratedFDeriv_comp_le_of_contDiffAt_ste` is proved below.  Both reviewers
had approved the statement; the proof follows their route: two open neighbourhoods obtained from
`ContDiffAt.contDiffOn` (shrunk to balls via `mem_nhds_iff`/`Metric.mem_nhds_iff`, with `MapsTo`
from `ContDiffAt.continuousAt.preimage_mem_nhds`), `IsOpen.uniqueDiffOn` on both, Mathlib's
`norm_iteratedFDerivWithin_comp_le`, and `iteratedFDerivWithin_of_isOpen` to convert the within
norms on both sides to the plain `iteratedFDeriv` norms.

```lean
theorem norm_iteratedFDeriv_comp_le_of_contDiffAt_ste {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g : F → Z) (f : E → F) (x : E) (k : ℕ) (C D : ℝ)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (f x)) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ (Nat.factorial k : ℝ) * C * D ^ k
```
(The `request_lemma` for this path was refused repeatedly — "the team is busy" — and it was then
proved by hand; it is *available*, so (b) below is now unblocked and can use this one directly
instead of the still-`sorry`ing EXT module.)

**Exact ingredients (located in Mathlib, this session).**  The assembly is now mechanical:

* `norm_iteratedFDerivWithin_comp_le` (`Analysis/Calculus/ContDiff/Bounds.lean:446`):
  ```lean
  (hg : ContDiffOn 𝕜 N g t) (hf : ContDiffOn 𝕜 N f s) (hn : n ≤ N)
  (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hst : MapsTo f s t) (hx : x ∈ s)
  (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
  (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin 𝕜 i f s x‖ ≤ D ^ i) :
  ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ ≤ n ! * C * D ^ n
  ```
* `iteratedFDerivWithin_of_isOpen (n) (hs : IsOpen s) : ∀ x ∈ s, iteratedFDerivWithin 𝕜 n f s x = iteratedFDeriv 𝕜 n f x`
  (`Analysis/Calculus/ContDiff/FTaylorSeries.lean:908`) — this converts the *within* norms in the
  `hC`/`hD` hypotheses and in the conclusion to the plain `iteratedFDeriv` norms of the statement.
* `ContDiffWithinAt.contDiffOn (hm : m ≤ n) (h' : m = ∞ → n = ω)` (`Analysis/Calculus/ContDiff/Defs.lean:511`)
  — turns `ContDiffAt ℝ ⊤ f x` (= `ContDiffWithinAt ℝ ⊤ f univ x`) into `ContDiffOn ℝ k f t` with
  `t ∈ 𝓝 x` (for `k : ℕ` the side condition `h'` is vacuous); apply it twice, to `g` on a ball
  around `f x` and to `f` on a ball around `x`.
* `hst : MapsTo f s t` from continuity of `f` at `x` (`ContDiffAt.continuousAt`, then
  `Metric.mem_nhds_iff`), by shrinking the ball around `x`.
* `UniqueDiffOn` on the two open balls (open ⇒ `UniqueDiffOn`; locate `IsOpen.uniqueDiffOn` /
  use `uniqueDiffOn_univ` after replacing with `univ` where possible).

Once green, (b) is the two-line instantiation at `W := fun y => (y, V y)`.

### (d) the sharp `L^{2p}` bound — **PROVED (fleet agent)**

`Work.Diff.STE.norm_seriesFun_rpow_le`, module `Diff/STE/flat/norm_seriesFun_rpow_le` (builds,
sorry-free; it brings a `Diff/STE/flat/Sobolev` helper module with the Littlewood–Paley-style
machinery).  Its statement is below.
(module `Diff/STE/flat/norm_seriesFun_rpow_le`; reviewed by both reviewers.)

```lean
theorem norm_seriesFun_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 1 ≤ p) (j : ℝ)
    (hj : (Fintype.card ι : ℝ) * (1 / 2 - 1 / (2 * p)) < j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => ((Work.Diff.STE.wt k) ^ j) * ‖γ k‖ ^ 2) →
      (∫ x in Work.Diff.STE.unitCube (ι := ι),
          ‖Work.Diff.STE.seriesFun γ x‖ ^ (2 * p)) ^ (1 / (2 * p))
        ≤ C * (∑' k : ι → ℤ, ((Work.Diff.STE.wt k) ^ j) * ‖γ k‖ ^ 2) ^ (1 / 2)
```
(module `Diff/STE/flat/norm_seriesFun_rpow_le`; imports `Diff/STE/Torus`,
`Diff/STE/summable_wt_zpow`, `Diff/STE/Comp/young_conv_lp`.)  Note `(wt k) ^ j = ⟨k⟩^{2j}` is the
level-`j` weight.

**Warning (found while planning the proof, no code yet).**  The sharp level here is
`j > n/2 - n/(2p)`; the *elementary* routes do **not** give it:
* the `p`-fold Young route (`Comp.young_conv_lp`) combined with Hölder in the weights
  (`∑_k ‖γ k‖^p ≤ (∑_k ⟨k⟩^{2j}‖γ k‖²)^{p/2}(∑_k ⟨k⟩^{-2jp/(2-p)})^{(2-p)/2}`) needs
  `2jp/(2-p) > n`, i.e. `j > n(2-p)/(2p)`, which for `p = 2` is `j > 0` — but the *sharper* step
  `‖iConv p γ‖_{ℓ²} ≥ …` loses a factor, and in fact that route only proves the *sup-level* bound
  (level `> n/2`); counterexample: `γ k = a` on a ball of radius `M` gives `‖f‖_4 ≍ M^{n/2} a`
  while the elementary majorant is `M^{3n/8}a^{1/2}`;
* consequently the plan's product estimates must use the *sharp* (fractional-order) Sobolev
  embedding, i.e. `norm_seriesFun_rpow_le` above, proved by Littlewood–Paley / real interpolation
  (this is the single genuinely new ingredient the a priori estimate needs).

The two statements above were reviewed (`request_review` on
`Diff/STE/flat/hasDerivAt_ENormSq_seriesFun` and `Diff/STE/flat/norm_seriesFun_rpow_le`); the
`request_lemma` calls were still being refused ("the team is busy") at the time of writing, so the
continuation should retry them first.

### Honest sibling of (d): the crude `L^{2p}` bound at an integer level `s > n/2`

*Not* the sharp bound, but a permanent lemma and the `(0, n/2)`-route input of the numerology:

```lean
theorem norm_seriesFun_Lp_le {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℝ) (hp : 1 ≤ p)
    (s : ℕ) (hs : Fintype.card ι < 2 * s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ γ : (ι → ℤ) → ℂ,
      Summable (fun k : ι → ℤ => (wt k) ^ s * ‖γ k‖ ^ 2) →
      (∫ x in unitCube, ‖seriesFun γ x‖ ^ (2 * p)) ^ (1 / (2 * p))
        ≤ C * (∑' k : ι → ℤ, (wt k) ^ s * ‖γ k‖ ^ 2) ^ (1 / 2)
```
Route: `norm_seriesFun_le s hs` bounds `‖seriesFun γ‖_∞` by `C₁ √(CSq s γ)`; the `L²` isometry
`integral_normSq_seriesFun` (whose `ℓ¹` hypothesis follows from the level-`s` square summability by
AM–GM against `∑ (wt)⁻ˢ`, summable by `summable_wt_zpow`) computes `∫ ‖seriesFun γ‖²`; Hölder /
`Real.rpow` interpolation of the two gives `(C₁ √(CSq s γ))^{1-1/p} (CSq s γ)^{1/(2p)}`.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.ENormSq_seriesFun_le
import Submission.Work.Diff.STE.hasDerivAt_integral_normSq_seriesFun
import Submission.Work.Diff.STE.gronwall_linear_bound
import Submission.Work.Diff.STE.flat.pairing_bound_sharp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory BigOperators Filter

namespace Work.Diff.STE.flat

/-- `ENormSq 0` is the plain `L²` norm squared over the unit cube. -/
lemma ENormSq_zero_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → ℂ) :
    ENormSq 0 f = ∫ x in unitCube, ‖f x‖ ^ 2 := by
  rw [ENormSq]
  have hpd : pdVec (ι := ι) 0 (Classical.arbitrary (Fin 0 → ι)) f = f := by
    simp [pdVec, pdList]
  rw [Finset.sum_eq_single (Classical.arbitrary (Fin 0 → ι))]
  · rw [hpd]
  · intro b _ hb
    exact absurd (Subsingleton.elim b (Classical.arbitrary (Fin 0 → ι))) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Time derivative of the flat `Hᵏ` energy of a Fourier series** (the "differentiate the
energy" step of the a priori estimate).  If every coefficient of `c` is differentiable everywhere
with derivative `cdot`, if all polynomial moments of `cdot` are summable and if `c` is locally
uniformly dominated by a family all of whose polynomial moments are summable, then
`s ↦ ENormSq k (seriesFun (c s)) + ENormSq 0 (seriesFun (c s))` has at `t` the derivative
`2 * (∑ l : Fin k → ι, L2re (seriesFun (dmulV (List.ofFn l) cdot)) (seriesFun (dmulV (List.ofFn l) (c t)))) + 2 * L2re (seriesFun cdot) (seriesFun (c t))`. -/
theorem hasDerivAt_ENormSq_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (c : ℝ → (ι → ℤ) → ℂ) (cdot : (ι → ℤ) → ℂ) (t : ℝ)
    (hc : ∀ m : ι → ℤ, ∀ s : ℝ, HasDerivAt (fun σ => c σ m) (cdot m) s)
    (hdom : ∀ N : ℕ, Summable fun m : ι → ℤ => (wt m) ^ N * ‖cdot m‖)
    (hb : ∃ b : (ι → ℤ) → ℝ,
      (∀ N : ℕ, Summable fun m : ι → ℤ => (wt m) ^ N * b m) ∧
      Filter.Eventually (fun s : ℝ => ∀ m : ι → ℤ, ‖c s m‖ ≤ b m) (nhds t)) :
    HasDerivAt (fun s => ENormSq k (seriesFun (c s)) + ENormSq 0 (seriesFun (c s)))
      (2 * (∑ l : Fin k → ι, L2re (seriesFun (dmulV (List.ofFn l) cdot))
            (seriesFun (dmulV (List.ofFn l) (c t))))
        + 2 * L2re (seriesFun cdot) (seriesFun (c t))) t := by
  obtain ⟨b, hbmom, hbev⟩ := hb
  have hbm0 : Summable b := by simpa using hbmom 0
  have hdom0 : Summable (fun m : ι → ℤ => ‖cdot m‖) := by simpa using hdom 0
  -- moment summability of `c s` as soon as it is dominated by `b`
  have hmom : ∀ s : ℝ, (∀ m : ι → ℤ, ‖c s m‖ ≤ b m) →
      ∀ N : ℕ, Summable fun m : ι → ℤ => (wt m) ^ N * ‖c s m‖ := by
    intro s hs N
    refine Summable.of_nonneg_of_le
      (fun m => mul_nonneg (pow_nonneg (wt_pos m).le N) (norm_nonneg _)) (fun m => ?_)
      (hbmom N)
    exact mul_le_mul_of_nonneg_left (hs m) (pow_nonneg (wt_pos m).le N)
  -- each high order summand is differentiable
  have hsm : ∀ l : Fin k → ι,
      HasDerivAt (fun s => ∫ x in unitCube, ‖seriesFun (dmulV (List.ofFn l) (c s)) x‖ ^ 2)
        (2 * L2re (seriesFun (dmulV (List.ofFn l) cdot))
          (seriesFun (dmulV (List.ofFn l) (c t)))) t := by
    intro l
    refine hasDerivAt_integral_normSq_seriesFun
      (fun s m => dmulV (List.ofFn l) (c s) m) (dmulV (List.ofFn l) cdot) t ?_ ?_ ?_
    · intro m s
      have h := (hc m s).const_mul ((List.ofFn l).map
        (fun i => (2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)))).prod
      simpa [dmulV] using h
    · simpa using summable_dmulV (List.ofFn l) cdot hdom 0
    · refine ⟨fun m => (2 * Real.pi) ^ (List.ofFn l).length *
          ((wt m) ^ (List.ofFn l).length * b m), (hbmom _).mul_left _, ?_⟩
      filter_upwards [hbev] with s hs m
      calc ‖dmulV (List.ofFn l) (c s) m‖
          ≤ (2 * Real.pi * wt m) ^ (List.ofFn l).length * ‖c s m‖ := norm_dmulV_le _ _ _
        _ ≤ (2 * Real.pi * wt m) ^ (List.ofFn l).length * b m :=
            mul_le_mul_of_nonneg_left (hs m)
              (pow_nonneg (mul_nonneg (by positivity) (le_of_lt (wt_pos m))) _)
        _ = (2 * Real.pi) ^ (List.ofFn l).length *
              ((wt m) ^ (List.ofFn l).length * b m) := by rw [mul_pow]; ring
  -- the high order energy agrees with the sum of the differentiated series near `t`
  have hev : (fun s => ENormSq k (seriesFun (c s)))
      =ᶠ[nhds t] fun s => ∑ l : Fin k → ι,
        ∫ x in unitCube, ‖seriesFun (dmulV (List.ofFn l) (c s)) x‖ ^ 2 := by
    filter_upwards [hbev] with s hs
    rw [ENormSq]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [show pdVec k l (seriesFun (c s)) = seriesFun (dmulV (List.ofFn l) (c s)) from
      funext (pdList_seriesFun (List.ofFn l) (c s) (hmom s hs))]
  have hsum : HasDerivAt (fun s => ∑ l : Fin k → ι,
        ∫ x in unitCube, ‖seriesFun (dmulV (List.ofFn l) (c s)) x‖ ^ 2)
      (2 * (∑ l : Fin k → ι, L2re (seriesFun (dmulV (List.ofFn l) cdot))
        (seriesFun (dmulV (List.ofFn l) (c t))))) t := by
    have h := HasDerivAt.fun_sum (u := Finset.univ)
      (A := fun l s => ∫ x in unitCube, ‖seriesFun (dmulV (List.ofFn l) (c s)) x‖ ^ 2)
      (A' := fun l => 2 * L2re (seriesFun (dmulV (List.ofFn l) cdot))
        (seriesFun (dmulV (List.ofFn l) (c t)))) (x := t) (fun l _ => hsm l)
    simpa [Finset.mul_sum] using h
  have hk_part : HasDerivAt (fun s => ENormSq k (seriesFun (c s)))
      (2 * (∑ l : Fin k → ι, L2re (seriesFun (dmulV (List.ofFn l) cdot))
        (seriesFun (dmulV (List.ofFn l) (c t))))) t :=
    hsum.congr_of_eventuallyEq hev
  have h0_part : HasDerivAt (fun s => ENormSq 0 (seriesFun (c s)))
      (2 * L2re (seriesFun cdot) (seriesFun (c t))) t := by
    have h := hasDerivAt_integral_normSq_seriesFun c cdot t hc hdom0 ⟨b, hbm0, hbev⟩
    simpa only [ENormSq_zero_eq, L2re] using h
  exact hk_part.add h0_part

/-- **Grönwall on a half-open interval** (architecture step (e)).

If `E` has derivative `E'` at every point of `Ico 0 T`, if `E' ≤ C * (1 + E)` there for some
`C ≥ 0`, and if `E 0 ≤ B`, then `E t ≤ (B + 1) * exp (C * t) - 1` for every `t ∈ Ico 0 T`.

This is the form in which the differential inequality of the a priori estimate arises (the
derivative hypothesis is available on the half-open interval only); it is reduced to
`Work.Diff.STE.gronwall_linear_bound` applied to the closed interval `[0, t]` for each `t < T`,
where all the hypotheses are available. -/
theorem gronwall_Ico {E E' : ℝ → ℝ} {T C B : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ t ∈ Set.Ico (0 : ℝ) T, HasDerivAt E (E' t) t)
    (hineq : ∀ t ∈ Set.Ico (0 : ℝ) T, E' t ≤ C * (1 + E t))
    (h0 : E 0 ≤ B) :
    ∀ t ∈ Set.Ico (0 : ℝ) T, E t ≤ (B + 1) * Real.exp (C * t) - 1 := by
  intro t ht
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Ico (0 : ℝ) T :=
    fun s hs => ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  exact Work.Diff.STE.gronwall_linear_bound hC
    (fun s hs => (hderiv s (hsub hs)).hasDerivWithinAt)
    (fun s hs => hineq s (hsub hs)) h0 t ⟨ht.1, le_rfl⟩

/-- **Faà di Bruno (chain-rule) bound for iterated derivatives, in the `ContDiffAt` form.**
Mathlib's `norm_iteratedFDeriv_comp_le` proves this under *global* smoothness of `g` and `f`; here
both are only smooth at the relevant points, which is what the applications need. -/
theorem norm_iteratedFDeriv_comp_le_of_contDiffAt_ste {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (g : F → Z) (f : E → F) (x : E) (k : ℕ) (C D : ℝ)
    (hg : ContDiffAt ℝ (⊤ : ℕ∞) g (f x)) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (hC : ∀ i ≤ k, ‖iteratedFDeriv ℝ i g (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDeriv ℝ i f x‖ ≤ D ^ i) :
    ‖iteratedFDeriv ℝ k (g ∘ f) x‖ ≤ (Nat.factorial k : ℝ) * C * D ^ k := by
  classical
  have hlev : ((((k : ℕ) : ENat)) : WithTop ENat) ≤ ((⊤ : ENat) : WithTop ENat) := WithTop.coe_le_coe.mpr le_top
  have hne : ((((k : ℕ) : ENat)) : WithTop ENat) = ((⊤ : ENat) : WithTop ENat) →
      ((⊤ : ENat) : WithTop ENat) = ⊤ := by
    intro h
    exact absurd (WithTop.coe_eq_coe.mp h) (ENat.natCast_ne_top k)
  -- neighbourhoods on which `g` resp. `f` are `C^k`
  obtain ⟨u, hu, hug⟩ : ∃ u ∈ nhds (f x),
      ContDiffOn ℝ ((((k : ℕ) : ENat)) : WithTop ENat) g u := hg.contDiffOn hlev hne
  obtain ⟨v, hv, hvf⟩ : ∃ v ∈ nhds x,
      ContDiffOn ℝ ((((k : ℕ) : ENat)) : WithTop ENat) f v := hf.contDiffOn hlev hne
  obtain ⟨t, ht_sub, ht_open, hft⟩ := mem_nhds_iff.mp hu
  obtain ⟨s, hs_sub, hs_open, hxs⟩ := mem_nhds_iff.mp hv
  -- shrink `s` so that `f` maps it into `t`
  have hpre : f ⁻¹' t ∈ nhds x := hf.continuousAt.preimage_mem_nhds (ht_open.mem_nhds hft)
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hs'_open : IsOpen (s ∩ Metric.ball x ρ) := hs_open.inter Metric.isOpen_ball
  have hx' : x ∈ s ∩ Metric.ball x ρ := ⟨hxs, Metric.mem_ball_self hρ⟩
  have hst : Set.MapsTo f (s ∩ Metric.ball x ρ) t := fun y hy => hρsub hy.2
  -- apply the `within` Faà di Bruno bound on these two open sets
  have h := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := k)
    (g := g) (f := f) (s := s ∩ Metric.ball x ρ) (t := t) (x := x)
    (hug.mono ht_sub) (hvf.mono (Set.Subset.trans Set.inter_subset_left hs_sub))
    le_rfl ht_open.uniqueDiffOn hs'_open.uniqueDiffOn hst hx'
    (fun i hi => by
      rw [show iteratedFDerivWithin ℝ i g t (f x) = iteratedFDeriv ℝ i g (f x) from
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i ht_open hft]
      exact hC i hi)
    (fun i hi₁ hi₂ => by
      rw [show iteratedFDerivWithin ℝ i f (s ∩ Metric.ball x ρ) x = iteratedFDeriv ℝ i f x from
        iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) i hs'_open hx']
      exact hD i hi₁ hi₂)
  rwa [show iteratedFDerivWithin ℝ k (g ∘ f) (s ∩ Metric.ball x ρ) x
      = iteratedFDeriv ℝ k (g ∘ f) x from
    iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) k hs'_open hx'] at h

/-- A coefficient family supported in the Galerkin box has all its weighted moments summable.

This supplies the `hdom`/`hbd` hypotheses of
`Work.Diff.STE.flat.hasDerivAt_ENormSq_seriesFun_nhds` for families supported in the box (the
projected velocities of a Galerkin trajectory are box-supported by construction), and the `hdom` of
`Work.Diff.STE.flat.hasDerivAt_ENormSq_seriesFun`. -/
lemma summable_wt_mul_of_box {n : ℕ} (N : ℕ) (f : (Fin n → ℤ) → ℂ)
    (hf : ∀ m : Fin n → ℤ, m ∉ Work.Diff.STE.Flat.box n N → f m = 0) (M : ℕ) :
    Summable fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * ‖f m‖ := by
  have hzero : ∀ m : Fin n → ℤ, m ∉ Work.Diff.STE.Flat.box n N →
      (Work.Diff.STE.wt m) ^ M * ‖f m‖ = 0 := by
    intro m hm
    rw [hf m hm, norm_zero, mul_zero]
  have hnn : ∀ m : Fin n → ℤ, 0 ≤ (Work.Diff.STE.wt m) ^ M * ‖f m‖ := fun m =>
    mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) M) (norm_nonneg _)
  refine summable_of_sum_le
    (f := fun m : Fin n → ℤ => (Work.Diff.STE.wt m) ^ M * ‖f m‖)
    (c := ∑ m ∈ Work.Diff.STE.Flat.box n N, (Work.Diff.STE.wt m) ^ M * ‖f m‖) hnn fun s => ?_
  calc ∑ m ∈ s, (Work.Diff.STE.wt m) ^ M * ‖f m‖
      ≤ ∑ m ∈ s ∪ Work.Diff.STE.Flat.box n N, (Work.Diff.STE.wt m) ^ M * ‖f m‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left) (fun m _ _ => hnn m)
    _ = ∑ m ∈ Work.Diff.STE.Flat.box n N, (Work.Diff.STE.wt m) ^ M * ‖f m‖ :=
        (Finset.sum_subset (Finset.subset_union_right) (fun m _ hm => hzero m hm)).symm

theorem energy_apriori {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun s => c s k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c t) x) i j * v i * v j) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t)) ≤ B ^ 2) →
        ∀ t ∈ Set.Ico (0 : ℝ) Tc,
          Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c t))
            ≤ (Work.Diff.STE.Flat.ENormSqFull k (Work.Diff.STE.Flat.seriesFunM (c 0)) + 1)
                * Real.exp (C * t) - 1 := by
  exact energy_apriori_of_pairing_sharp hn Φ hshape k lam hlam B
    (pairingBoundSharp_of_pieces hn Φ hshape k hk lam hlam B hB)

end Work.Diff.STE.flat

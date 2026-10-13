import Mathlib
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilCrux.fibreDerivBound

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c.C1Direct

/-!
## The parameter-direction step of the G4c crux (map N4c5, `PathGainBound`)

This file is the G4c-side anchor for the map's node **N4c5** — the *pure real-analysis* step of
the flat-sheet normal form (`sources/wilkiesG4/wilkies_g4c_crux_map.md`, §2.3).  Addendum 10 of
`Submission/Work/WilG4c/C1AllComplThinClean_NOTES.md` records that this step is **not** bypassable
by the Fubini/measure route: a definable set with uniformly small `k`-slices may still have a fat
closure-trace on the sheet (the "bad sheet" shape), so the contradiction must come from the
*transversality* estimate below, not from a measure count.

### The estimate and its accounting

Let `F s := famFun G (Fin.append (w₁ + s • e_i) (ψ s))` — the joint function along the path
`s ↦ (w₁ + s e_i, ψ s)`.  Off the `≤ K` break points `brk`, `F` is differentiable (`hC1` at the
path point together with `hdiff` for `ψ`), and

* `fderiv_append_split` splits the direction `(e_i, ψ' s)` exactly into `(e_i, 0)` and `(0, ψ' s)`;
* the first summand is `≥ η` by `hgain`;
* the second summand is `≥ −M · Σ_k |ψ_k' s|` by `FibrePartialBoundClosed` (fibre partials bounded
  by `M` on the **closed** `τ`-ball) together with `‖v‖ ≤ Σ_k |v k|`.

Integrating over each of the `≤ K+1` pieces: the rise is `≥ η·(length) − M·Σ_k ∫|ψ_k'|`, and
`MonotonePathIntegral` gives `∫|ψ_k'| ≤ 2τ` on each piece (coordinatewise monotonicity plus
`|ψ_k| ≤ τ`).  At each of the `≤ K` interior break points the jump of `F` costs at most `2Mτ`
(`hLip`: the two sphere points are within `2τ`).  The endpoints cost `≤ Mτ` each (`hsmall` with
`‖ψ‖ = τ`).  Summing:
`η L − 2Mb(K+1)τ − 2MKτ ≤ F L − F 0 ≤ 2Mτ`, hence `η L ≤ (K+2)(2(b+1)M + 1)τ`, with slack
`≈ 2bM + 2M + K + 2 ≥ 0`.

### Supporting pieces (sibling files)

* `Work.WilG4c.C1Direct.MonotonePathIntegral` — the one-variable input
  (`∫ |deriv p| ≤ 2R` on a monotone piece);
* `Work.WilG4c.C1Direct.FibrePartialBound` (proved) and
  `Work.WilG4c.C1Direct.FibrePartialBoundClosed` — `M`-Lipschitzness in the second argument bounds
  the fibre partials by `M`, on the open and on the **closed** ball of radius `τ`.

Norm note: the norm on `Fin b → ℝ` in this development is the **sup** norm, and that is what makes
the closed-ball fibre-partial bound sharp at the sphere points: the ball's boundary is a union of
faces, so for each coordinate direction at least one of `z ± h • e_k` stays inside the ball.
-/

/-- **N4c5 (`PathGainBound`).**  Along `s ↦ (w₁ + s e_i, ψ s)` with `‖ψ s‖ = τ`, piecewise `C¹`
and coordinatewise monotone (at most `K` breaks), if `∂_{w_i} G ≥ η` on the path, `G` is
`M`-Lipschitz in `z` on the `τ`-ball and `|G w z| ≤ M‖z‖`, then the gain `η L` is `O(τ)`. -/
theorem PathGainBound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (L τ M η : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hM : 0 ≤ M)
    (ψ : ℝ → (Fin b → ℝ)) (K : ℕ) (brk : Finset ℝ) (hbrk : brk.card ≤ K)
    (hsph : ∀ s ∈ Set.Icc 0 L, ‖ψ s‖ = τ)
    (hdiff : ∀ s ∈ Set.Ioo 0 L, s ∉ brk → DifferentiableAt ℝ ψ s)
    (hmono : ∀ k : Fin b, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ L → (∀ u ∈ Set.Ioo s t, u ∉ brk) →
      MonotoneOn (fun u => ψ u k) (Set.Ioo s t) ∨ AntitoneOn (fun u => ψ u k) (Set.Ioo s t))
    (hLip : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ), ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G w z - G w z'| ≤ M * ‖z - z'‖)
    (hsmall : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ), ‖z‖ ≤ τ → |G w z| ≤ M * ‖z‖)
    (hC1 : ∀ s ∈ Set.Icc 0 L, ∀ z : Fin b → ℝ, ‖z‖ = τ →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z))
    (hgain : ∀ s ∈ Set.Icc 0 L, η ≤ fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0)) :
    η * L ≤ ((K : ℝ) + 2) * (2 * ((b : ℝ) + 1) * M + 1) * τ := by
  sorry

/-- **The key structural step of the accounting.**  The derivative of `F` at a point, applied to
a direction `(e, v)`, splits as the sum of the pure parameter-direction application and the pure
fibre-direction application.  This is all the "partial derivative" bookkeeping the path-gain
accounting needs: `PathGainBound` bounds the first summand by `hgain` and the second by `hLip`
(through `FibrePartialBoundClosed`), so no explicit `fderiv`-of-`G` decomposition is required. -/
theorem fderiv_append_split {a b : ℕ} (F : (Fin (a + b) → ℝ) → ℝ) (p : Fin (a + b) → ℝ)
    (e : Fin a → ℝ) (v : Fin b → ℝ) :
    fderiv ℝ F p (Fin.append e v)
      = fderiv ℝ F p (Fin.append e 0) + fderiv ℝ F p (Fin.append 0 v) := by
  have h : Fin.append e v = Fin.append e (0 : Fin b → ℝ) + Fin.append (0 : Fin a → ℝ) v := by
    funext k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;>
      simp [Fin.append_left, Fin.append_right]
  rw [h, map_add]

/-- **The chain rule along the path `s ↦ (w₁ + s • e_i, ψ s)`.**

This is the derivative input of the accounting: at every point where `ψ` is differentiable and
the joint function is `C¹` at the corresponding path point, the one-variable function
`s ↦ famFun G (Fin.append (w₁ + s • Pi.single i 1) (ψ s))` has derivative
`fderiv (famFun G) (path s) (Fin.append (Pi.single i 1) (fderiv ψ s 1))` — which
`fderiv_append_split` then splits into the parameter part (bounded below by `hgain`) and the fibre
part (bounded by `hLip` through `FibrePartialBoundClosed`). -/
theorem path_hasDerivAt {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (ψ : ℝ → (Fin b → ℝ)) {s : ℝ}
    (hC1 : ContDiffAt ℝ 1 (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)))
    (hd : DifferentiableAt ℝ ψ s) :
    HasDerivAt (fun u : ℝ => Work.WilG4c.famFun G
        (Fin.append (w₁ + u • Pi.single i 1) (ψ u)))
      (fderiv ℝ (Work.WilG4c.famFun G)
        (Fin.append (w₁ + s • Pi.single i 1) (ψ s))
        (Fin.append (Pi.single i 1) (fderiv ℝ ψ s 1))) s := by
  have hdF : HasFDerivAt (Work.WilG4c.famFun G)
      (fderiv ℝ (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) (ψ s)))
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) :=
    hC1.differentiableAt_one.hasFDerivAt
  have hdψ : HasDerivAt ψ (fderiv ℝ ψ s 1) s := hd.hasFDerivAt.hasDerivAt
  have hpath : HasDerivAt (fun u : ℝ => Fin.append (w₁ + u • Pi.single i 1) (ψ u))
      (Fin.append (Pi.single i 1) (fderiv ℝ ψ s 1)) s := by
    rw [hasDerivAt_pi]
    intro k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · have h2 : HasDerivAt (fun u : ℝ => w₁ j + u * (Pi.single i 1 : Fin a → ℝ) j)
          (1 * (Pi.single i 1 : Fin a → ℝ) j) s :=
        ((hasDerivAt_id s).mul_const ((Pi.single i 1 : Fin a → ℝ) j)).const_add (w₁ j)
      have h1 : HasDerivAt (fun u : ℝ => (w₁ + u • (Pi.single i 1 : Fin a → ℝ)) j)
          ((Pi.single i 1 : Fin a → ℝ) j) s := by
        simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul] using h2
      simpa [Fin.append_left] using h1
    · have h2 := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin b => ℝ) j).hasFDerivAt
        |>.comp_hasDerivAt (x := s) hdψ
      simpa [Fin.append_right, Function.comp_def, ContinuousLinearMap.proj_apply] using h2
  simpa [Function.comp_def] using hdF.comp_hasDerivAt (x := s) hpath

/-- **Endpoint bound of the accounting.**  On the sphere of radius `τ`, the path value is bounded
by `Mτ` (this is `hsmall` at the path point). -/
theorem path_endpoint_bound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (ψ : ℝ → (Fin b → ℝ)) {τ M s : ℝ} (hs : ‖ψ s‖ = τ)
    (hsmall : ∀ (w : Fin a → ℝ) (z : Fin b → ℝ), ‖z‖ ≤ τ → |G w z| ≤ M * ‖z‖) :
    |Work.WilG4c.famFun G (Fin.append (w₁ + s • Pi.single i 1) (ψ s))| ≤ M * τ := by
  have hval : Work.WilG4c.famFun G (Fin.append (w₁ + s • Pi.single i 1) (ψ s))
      = G (w₁ + s • Pi.single i 1) (ψ s) := by
    simp only [Work.WilG4c.famFun, Fin.append_left, Fin.append_right]
  rw [hval]
  have hle : ‖ψ s‖ ≤ τ := le_of_eq hs
  calc |G (w₁ + s • Pi.single i 1) (ψ s)| ≤ M * ‖ψ s‖ := hsmall _ _ hle
    _ = M * τ := by rw [hs]

/-- **Final arithmetic of the accounting.**  From
`F L − F 0 ≤ 2Mτ` and `F L − F 0 ≥ ηL − 2Mbτ(K+1) − 2MτK`, conclude the map's bound
`ηL ≤ (K+2)(2(b+1)M + 1)τ` (the slack is `2bM + 2M + K + 2`). -/
theorem gain_arithmetic {K b : ℕ} {M η L τ A : ℝ} (hM : 0 ≤ M) (hτ : 0 ≤ τ)
    (hA : A ≤ 2 * M * τ)
    (h : A ≥ η * L - M * (2 * (b : ℝ)) * τ * ((K : ℝ) + 1) - 2 * M * τ * (K : ℝ)) :
    η * L ≤ ((K : ℝ) + 2) * (2 * ((b : ℝ) + 1) * M + 1) * τ := by
  have hK : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hb : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
  nlinarith [hA, h, hM, hτ, hK, hb, mul_nonneg hM hτ, mul_nonneg (mul_nonneg hb hM) hτ,
    mul_nonneg (mul_nonneg (mul_nonneg hb hM) hτ) hK]

/-- **The break-jump bound (item 2 of the accounting).**  At a break `s₀` the path value may jump,
because `ψ` may be discontinuous there; but the jump is at most `2Mτ`, and it is charged **once per
break**.

That is the *shape* item 2 needed to settle.  Write `F⁻` and `F⁺` for the one-sided values of the
path function at `s₀` (they exist because `ψ` has one-sided limits there, see
`path_onesided_limit`).  Since both limits lie on the sphere of radius `τ`, the `w`-coordinate is
the *same* `w₁ + s₀ • e_i` on both sides, and `G (w₁ + s₀ • e_i)` is `M`-Lipschitz in its fibre
argument on the closed `τ`-ball,

  `|F⁺ − F⁻| ≤ M‖Lp − Lm‖ ≤ M(‖Lp‖ + ‖Lm‖) = 2Mτ`.

In the telescope of the accounting the two one-sided values of the *same* node cancel against each
other, so each of the `≤ K` breaks costs `2Mτ` exactly once — which is what makes the `2Mτ·K` term
come out; a "surrounding" partition (two extra nodes per break, `4Mτ` per break) would break the
`K`-coefficient of the constant. -/
theorem path_jump_le {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) {τ M s₀ : ℝ} {Lm Lp : Fin b → ℝ} (hM : 0 ≤ M)
    (hLip : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ), ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G w z - G w z'| ≤ M * ‖z - z'‖)
    (hmτ : ‖Lm‖ = τ) (hpτ : ‖Lp‖ = τ) :
    Work.WilG4c.famFun G (Fin.append (w₁ + s₀ • Pi.single i 1) Lp)
      - Work.WilG4c.famFun G (Fin.append (w₁ + s₀ • Pi.single i 1) Lm) ≥ -(2 * M * τ) := by
  have hval : ∀ z : Fin b → ℝ, Work.WilG4c.famFun G
      (Fin.append (w₁ + s₀ • Pi.single i 1) z) = G (w₁ + s₀ • Pi.single i 1) z := by
    intro z
    simp only [Work.WilG4c.famFun, Fin.append_left, Fin.append_right]
  rw [hval Lp, hval Lm]
  set Δ := G (w₁ + s₀ • Pi.single i 1) Lp - G (w₁ + s₀ • Pi.single i 1) Lm with hΔ
  have h1 : |Δ| ≤ M * ‖Lp - Lm‖ := hLip _ _ _ (le_of_eq hpτ) (le_of_eq hmτ)
  have h2 : ‖Lp - Lm‖ ≤ 2 * τ := by
    calc ‖Lp - Lm‖ ≤ ‖Lp‖ + ‖Lm‖ := norm_sub_le _ _
      _ = τ + τ := by rw [hpτ, hmτ]
      _ = 2 * τ := by ring
  have h3 : |Δ| ≤ 2 * M * τ := by
    calc |Δ| ≤ M * ‖Lp - Lm‖ := h1
      _ ≤ M * (2 * τ) := mul_le_mul_of_nonneg_left h2 hM
      _ = 2 * M * τ := by ring
  linarith [neg_abs_le Δ, h3]

/-- **The fibre-direction derivative of `famFun` is the slice derivative.**

`famFun G` is the uncurried `G`, so a pure fibre direction `(0, v)` is differentiated by the slice
`G w` alone.  This is what lets `FibrePartialBoundClosed` bound the fibre summand of the
`fderiv_append_split` decomposition by `M · Σ_k |v k|`: `fderiv (G w) z v = Σ_k v k • fderiv (G w) z (e_k)`.

Proof route: `famFun G ∘ (fun z' => Fin.append w z') = G w` (by
`famFun (Fin.append w z') = G w z'`), and `z' ↦ Fin.append w z'` is the linear map whose derivative
at `z` applied to `v` is `Fin.append 0 v`; chain rule.  (The corresponding statement for the
parameter direction is not needed: `hgain` supplies that summand directly.) -/
theorem fderiv_famFun_fibre {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z v : Fin b → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z)) :
    fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append 0 v)
      = fderiv ℝ (G w) z v :=
  Work.WilCrux.fderiv_famFun_fibre G w z v hd

/-- **Item 3, the open piece.**

On a sub-interval `(l, r)` of `(0,L)` that contains no break, the path function gains at least
`η(r−l) − M·2bτ`.  The FTC gives the gain as the integral of the derivative; that derivative has
the pointwise lower bound `η − M·Σ_k |ψ_k'|` (`fderiv_append_split`, `hgain`,
`FderivFamFunFibre` + `FibrePartialBoundClosed`), and `MonotonePathIntegral` bounds
`∫_l^r |ψ_k'| ≤ 2τ` coordinatewise.

The conclusion is stated in terms of the **one-sided values** of the path function at `l` and `r`,
because `l`, `r` need not be points of continuity of `ψ`: those values are
`famFun G (w₁ + l • e_i, Lm)` and `famFun G (w₁ + r • e_i, Lp)` for the one-sided limits `Lm`,
`Lp` of `ψ` (whose existence, with `‖Lm‖ = ‖Lp‖ = τ`, is `PathOneSidedLimit`; for pieces whose
endpoints are not breaks they are `ψ l`, `ψ r` by continuity).  Continuity of `famFun G` *at* those
two limit points is what the sphere-point `hC1` supplies.

The `IntervalIntegrable` hypothesis is carried because the FTOC-with-one-sided-values
(`integral_eq_sub_of_hasDerivAt_of_tendsto`) needs it and it is *not* implied by the stated
hypotheses (a monotone differentiable coordinate may have unbounded derivative, e.g. `√(s−l)`).
In the map's N4 use the derivative field is `Ω`-definable hence locally bounded, so the assembly
discharges it there; see Addendum 14 of the notes. -/
theorem path_piece_bound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (ψ : ℝ → (Fin b → ℝ)) {τ M η L : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hsph : ∀ s ∈ Set.Icc 0 L, ‖ψ s‖ = τ)
    {brk : Finset ℝ}
    (hdiff : ∀ s ∈ Set.Ioo 0 L, s ∉ brk → DifferentiableAt ℝ ψ s)
    (hmono : ∀ k : Fin b, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ L → (∀ x ∈ Set.Ioo s t, x ∉ brk) →
      MonotoneOn (fun x => ψ x k) (Set.Ioo s t) ∨ AntitoneOn (fun x => ψ x k) (Set.Ioo s t))
    (hLip : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ), ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G w z - G w z'| ≤ M * ‖z - z'‖)
    (hC1 : ∀ s ∈ Set.Icc 0 L, ∀ z : Fin b → ℝ, ‖z‖ = τ →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z))
    (hgain : ∀ s ∈ Set.Icc 0 L, η ≤ fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0))
    {l r : ℝ} (hl : l ∈ Set.Ioo 0 L) (hr : r ∈ Set.Ioo 0 L) (hlr : l < r)
    (hbrk : ∀ x ∈ Set.Ioo l r, x ∉ brk)
    {Lm Lp : Fin b → ℝ}
    (hlm : Filter.Tendsto ψ (nhdsWithin l (Set.Ioi l)) (nhds Lm))
    (hrp : Filter.Tendsto ψ (nhdsWithin r (Set.Iio r)) (nhds Lp))
    (hmτ : ‖Lm‖ = τ) (hpτ : ‖Lp‖ = τ)
    (hint : IntervalIntegrable (fun s : ℝ => fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s))
      (Fin.append (Pi.single i 1) (fderiv ℝ ψ s 1))) MeasureTheory.volume l r) :
    Work.WilG4c.famFun G (Fin.append (w₁ + r • Pi.single i 1) Lp)
      - Work.WilG4c.famFun G (Fin.append (w₁ + l • Pi.single i 1) Lm)
      ≥ η * (r - l) - M * (2 * (b : ℝ)) * τ := by
  sorry

/-- **Item 1 of the accounting: the pointwise derivative lower bound.**

Off the breaks, the derivative of the path function is at least
`η − M · Σ_k |ψ_k'(s)|`: `fderiv_append_split` splits the direction, `hgain` bounds the parameter
summand from below by `η`, and the fibre summand is `fderiv (G (w₁+s•e_i)) (ψ s) (fderiv ψ s 1)`
(`FderivFamFunFibre`), bounded in absolute value by `M · Σ_k |(fderiv ψ s 1) k|` because each fibre
partial at the sphere point `ψ s` is bounded by `M` (`FibrePartialBoundClosed`) and a continuous
linear functional expands in the standard basis.

Local copy of the statement; the delegated sibling `Work.WilG4c.C1Direct.PathDerivLowerBound`
carries the same statement. -/
theorem path_deriv_lower_bound_aux {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (ψ : ℝ → (Fin b → ℝ)) {τ M η L : ℝ} (hM : 0 ≤ M) (hτ : 0 < τ)
    (hsph : ∀ s ∈ Set.Icc 0 L, ‖ψ s‖ = τ)
    {brk : Finset ℝ}
    (hdiff : ∀ s ∈ Set.Ioo 0 L, s ∉ brk → DifferentiableAt ℝ ψ s)
    (hLip : ∀ (w : Fin a → ℝ) (z z' : Fin b → ℝ), ‖z‖ ≤ τ → ‖z'‖ ≤ τ →
      |G w z - G w z'| ≤ M * ‖z - z'‖)
    (hC1 : ∀ s ∈ Set.Icc 0 L, ∀ z : Fin b → ℝ, ‖z‖ = τ →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z))
    (hgain : ∀ s ∈ Set.Icc 0 L, η ≤ fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0))
    {s : ℝ} (hs : s ∈ Set.Ioo 0 L) (hsb : s ∉ brk) :
    η - M * (∑ k : Fin b, |(fderiv ℝ ψ s 1) k|)
      ≤ fderiv ℝ (Work.WilG4c.famFun G)
          (Fin.append (w₁ + s • Pi.single i 1) (ψ s))
          (Fin.append (Pi.single i 1) (fderiv ℝ ψ s 1)) := by
  have hsL : s ∈ Set.Icc 0 L := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
  have hspheq : ‖ψ s‖ = τ := hsph s hsL
  have hfib := Work.WilCrux.fibreDerivBound G (w₁ + s • Pi.single i 1) (ψ s)
    (fderiv ℝ ψ s 1) hM hτ (le_of_eq hspheq) (hC1 s hsL (ψ s) hspheq)
    (fun z z' hz hz' => hLip (w₁ + s • Pi.single i 1) z z' hz hz')
  have hgain' : η ≤ fderiv ℝ (Work.WilG4c.famFun G)
      (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Fin.append (Pi.single i 1) 0) := hgain s hsL
  rw [fderiv_append_split (Work.WilG4c.famFun G)
    (Fin.append (w₁ + s • Pi.single i 1) (ψ s)) (Pi.single i 1) (fderiv ℝ ψ s 1)]
  linarith [neg_abs_le (fderiv ℝ (Work.WilG4c.famFun G)
    (Fin.append (w₁ + s • Pi.single i 1) (ψ s))
    (Fin.append (0 : Fin a → ℝ) (fderiv ℝ ψ s 1))), hfib, hgain']

/-- **The one-sided limit of the path value, from that of `ψ`.**

If `ψ` tends to `Lm` along a filter `𝓵 ≤ 𝓝 l`, then the path value
`s ↦ famFun G (w₁ + s • e_i, ψ s)` tends to `famFun G (w₁ + l • e_i, Lm)` along `𝓵`.  This is what
lets `path_piece_bound` be applied at a *break*: the FTC with one-sided values asks for the
one-sided limits of the path function, and here they are, computed from those of `ψ`
(`PathOneSidedLimit`) together with the sphere-point `hC1`, which supplies continuity of
`famFun G` at the limit point `(w₁ + l • e_i, Lm)` — a point off the path when `ψ` is
discontinuous at `l`.

The parameter coordinate is continuous (`s ↦ w₁ + s • e_i`), the fibre coordinate tends to `Lm` by
hypothesis, and `tendsto_pi_nhds` assembles the two; then compose with the continuity of
`famFun G`.  Applied with `𝓵 := nhdsWithin l (Set.Ioi l)` and with `𝓵 := nhdsWithin r (Set.Iio r)`
it gives the two limits the FTC needs on the piece `(l, r)`. -/
theorem path_value_tendsto {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (w₁ : Fin a → ℝ) (ψ : ℝ → (Fin b → ℝ)) {τ L l : ℝ} {Lm : Fin b → ℝ} {𝓵 : Filter ℝ}
    (hC1 : ∀ s ∈ Set.Icc 0 L, ∀ z : Fin b → ℝ, ‖z‖ = τ →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append (w₁ + s • Pi.single i 1) z))
    (hl : l ∈ Set.Icc 0 L) (hmτ : ‖Lm‖ = τ)
    (hle : 𝓵 ≤ nhds l) (hlm : Filter.Tendsto ψ 𝓵 (nhds Lm)) :
    Filter.Tendsto (fun s : ℝ => Work.WilG4c.famFun G
        (Fin.append (w₁ + s • Pi.single i 1) (ψ s))) 𝓵
      (nhds (Work.WilG4c.famFun G (Fin.append (w₁ + l • Pi.single i 1) Lm))) := by
  have hcont : ContinuousAt (Work.WilG4c.famFun G) (Fin.append (w₁ + l • Pi.single i 1) Lm) :=
    (hC1 l hl Lm hmτ).continuousAt
  refine hcont.tendsto.comp ?_
  rw [tendsto_pi_nhds]
  intro k
  have hid : Filter.Tendsto (fun s : ℝ => s) 𝓵 (nhds l) := Filter.tendsto_id'.mpr hle
  refine Fin.addCases (fun j => ?_) (fun j => ?_) k
  · have h1 : Filter.Tendsto (fun s : ℝ => w₁ j + s * (Pi.single i 1 : Fin a → ℝ) j) 𝓵
        (nhds (w₁ j + l * (Pi.single i 1 : Fin a → ℝ) j)) :=
      tendsto_const_nhds.add (hid.mul tendsto_const_nhds)
    simpa [Fin.append_left, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1
  · have h2 : Filter.Tendsto (fun s : ℝ => ψ s j) 𝓵 (nhds (Lm j)) :=
      (tendsto_pi_nhds.mp hlm) j
    simpa [Fin.append_right] using h2

end Work.WilG4c.C1Direct

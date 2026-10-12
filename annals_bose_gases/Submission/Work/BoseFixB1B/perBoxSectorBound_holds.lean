import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.boxQ0_ge_a0MainBox
import Submission.Work.BoseFixB1.perSectorBoundG_holds
import Submission.Work.BoseFixB1S.perBoxGapBranchB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.perBoxSectorBound_holds` — FS `thm:smallbox` in sector form

`PerBoxSectorBound v h R` is the sector (mixture) form of FS `thm:smallbox` at the sliding
box `B(u)`: the `B(u)`-occupancy sector mixture of the count-indexed thresholds dominates
the localised word `sbWord = tBwordBInd + qLHSwordB`.

**Findings of this session** (see `FINDING_perBoxSectorBound.md` in this directory):

## STATUS (session 4) — read `FINDING_perBoxSectorBound_session4.md` FIRST

* the residual is now `PerBoxSectorBound v h R ⟸` **low-density arm (PROVED)** +
  `PerBoxSectorBoundDense`, assembled by `perBoxSectorBound_of_lowDensity_dense` (PROVED);
* **`a0Main_sharp_pays` (PROVED)**: the *sharp* `A₀`-payment.  Under the Born-gap margin
  `(6c + c²)M₁ ≤ (1 − 4c)(M₂ − M₁)` (equivalently `(1+c)²M₁ ≤ (1−4c)M₂`, the negative discriminant
  of `(M₂/2)τ² − (1+c)μτM₁ + (½−2c)μ²M₁`), the pair term pays the one-body line **uniformly in the
  density** `τ`; this is the arithmetic core of the dense arm;
* **the access to the pair term is PROVED**: `Work.BoseFixB1.bqPotsplit` is FS `lem:potsplit` at
  the *sliding* projections (`qLHSword = boxQSum`), and `boxQ0_ge_a0MainBox_slack` (s2) keeps the
  two-body pair mass, so `sbWord ≥ (M₂/2)(τ² − τ/V) − μτM₁ + (boxQ1+…+boxQ4) + tBwordBInd`.
  Hence the dense arm is **exactly** the q-row + kinetic rung (see the FINDING §1);
* the s3 compile defects are fixed; the low arm's hypothesis is the count-dominated form
  `(½−2c)·μ·∬w₁·‖Φ‖² ≥ (c·∬w₁/χ + ξ a v)·n‖Φ‖²`.

## STATUS (session 3) — read `FINDING_perBoxSectorBound_session3.md` FIRST

* the residual is split on the box-excited count `n₊(B(u))` into
  `PerBoxSectorBoundGap` (`n‖Φ‖² ≤ n₊`) and `PerBoxSectorBoundFlat` (`n₊ < n‖Φ‖²`), with the
  assembly `perBoxSectorBound_of_arms` and the monotonicity lemmas `mixLHS_mono_c` /
  `mixLHS_anti_C` — all **PROVED** (axiom-clean);
* the **gap arm `perBoxSectorBound_gap` is PROVED** (this session): `c := 1/4`, `C := 0`, using
  the *linear* `F`-bound `F(t) ≤ μ(t+μ)` — with `c = 1/4` the background cancels **exactly** —
  the count bound `Σ_k k m_k ≤ n‖Φ‖²`, the mass law `w1MassB ≤ C_W(a v)chiMass`, the FS gap
  payment `sbKin ≥ c'²μ(a v)n₊` and the uniform fibre bound `|w₁-fibre| ≤ (ξ a v)χ_B`;
* **`mixLHS_le_muWcnt`** (PROVED): `mixLHS h c C μ n Φ u ≤ c·μ·(∬w₁/χ)·Σ_k k m_k`;
* the **flat arm** is the one remaining obligation.  Its delegated prover returned
  `declare_false` (`FINDING_perBoxSectorBound_flat_false.md`), as did a sibling for `PerBoxF`
  (`FINDING_flatBranchAlt.md` §ADDENDUM); both rest on a *hand* estimate of the spectral half
  `tBwordKinInd` on pair-dead ("hole") states.  §4–§5 of
  `FINDING_perBoxSectorBound_session3.md` **refute that** verdict in principle: FS's own proof
  produces `R_Ψ = ⟨Ψ, ∫F(n_{B(u)}/|B|)∬w_{1,B}du Ψ⟩` with `n_{B(u)}` the **occupancy operator**
  (`final_v2.tex` l. 4065–4120), so the *mixture* form is FS's, and the per-state (operator)
  bound follows from the group-marginal form `e_B(n) ≥ m e_B(n') + e_B(n'')` of FS's split
  (`l. 3975–4065`), which forces `sbWord ≳ (a v)μn‖Φ‖²` on every state (in particular on the hole
  states).  The residual is therefore the *sharp* per-state/mixture FS bound at the corpus's
  localised word, not the (false) mean-field Cauchy–Schwarz layer.
* **do NOT re-attempt** `Work.BoseFixB1.lm_appinteraction_localised` / `bracketB1_nonneg` /
  `Work.BoseFixB1S.boxTheta_bound` / the `mf*` rows as the route to this file: they are
  *separated* (kinetic-free) potential estimates and are refuted by the pole-slab / corner
  mismatch (§2.1 of the session-3 FINDING).

Landed earlier (unchanged):

* `psiWeight_one_le_mu_mul_add`, `fWeight_sum_le` — FS's `F(t) ≤ μ(t+μ)` and the
  `F`-weight → count passage;
* `update_update_same`, `boxPInd_update_eq_of_mem` — the box projection `P = boxPInd` is
  *independent of the slot-`i` coordinate* on the box (the algebraic heart of the
  flat-part identities);
* `boxPInd_sq_mul_comp_localised` — the **box-mean flat-part identity** at the localised
  kernels: `|A ∩ acube ℓ|·∫(P_iΦ)²F(x_i) = (∫_{A∩acube ℓ}F)·∫(P_iΦ)²`.  `volA` cancels and
  the normaliser is the measure of `A ∩ acube ℓ`, *not* of `A` (in the FS regime
  `dℓ ≫ μ^{-1/3}`, so `B(u) ⊄ acube ℓ` and the `x_i`-integration only sees the
  intersection).  The proof is the single-slot Fubini peel `abox_integral_peel`
  (`Submission/Q0Sector.lean:347`) plus `kcInsN_update_zero` (`SectorProj.lean:339`).
-/

namespace Work.BoseFixB1B

open MeasureTheory
open _root_.BoseGases Submission.BoseGases Work.UBB
open Work.FockBridge Work.SmallBoxSliding Work.BoseBoxFix

/-- **FS's weight is dominated by `μ(t+μ)`**: `psiWeight 1 μ t = μ(t−μ)²/(t+μ) ≤ μ(t+μ)`
for `t ≥ 0` (indeed `(t−μ)² ≤ (t+μ)²`).  Proved here for self-containedness. -/
theorem psiWeight_one_le_mu_mul_add {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * (t + μ) := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have h1 : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have heq : μ * (t + μ) * (1 + t * μ⁻¹) = (t + μ) ^ 2 := by
    field_simp
    ring
  rw [heq]
  nlinarith [mul_nonneg ht hμ.le]

/-- **The `F`-weight of the sector mixture is bounded by the `μ(t+μ)`-weighted count**:
termwise `F(k/|B(u)|) ≤ μ(k/|B(u)| + μ)` and the sector masses are nonnegative.  This is the
first (elementary) step of the assembly of `PerBoxSectorBound`: it converts the positive
`F`-part of the residual's left-hand side into the two count quantities that the mean-field
square, the chemical-potential term and the backgrounds can pay. -/
theorem fWeight_sum_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} (hμ : 0 < μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ)) (u : EuclideanSpace ℝ (Fin 3)) :
    (∑ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : Submission.BoseGases.X n → ℝ) k
          * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / PBV v μ u))
      ≤ μ * ∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
            (Φ : Submission.BoseGases.X n → ℝ) k
            * ((k : ℝ) / PBV v μ u + μ) := by
  have hV : 0 ≤ PBV v μ u := by
    show 0 ≤ Work.SmallBoxSliding.chiMass (PBM v μ) (PBℓ v μ) (PBd v μ) u
    rw [Work.SmallBoxSliding.chiMass_def]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / PBV v μ u)
      ≤ μ * ((k : ℝ) / PBV v μ u + μ) :=
    psiWeight_one_le_mu_mul_add hμ (div_nonneg (Nat.cast_nonneg k) hV)
  have h2 := mul_le_mul_of_nonneg_left h1
    (Work.FockBridge.sectorMass_nonneg (PBℓ v μ) (PBB v μ u)
      (Φ : Submission.BoseGases.X n → ℝ) k)
  calc Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
          (Φ : Submission.BoseGases.X n → ℝ) k
        * Work.SmallBoxSliding.psiWeight 1 μ ((k : ℝ) / PBV v μ u)
      ≤ Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
          (Φ : Submission.BoseGases.X n → ℝ) k
        * (μ * ((k : ℝ) / PBV v μ u + μ)) := h2
    _ = μ * (Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
          (Φ : Submission.BoseGases.X n → ℝ) k
        * ((k : ℝ) / PBV v μ u + μ)) := by ring

/-! ## The flat-part identities at the localised kernels -/

/-- Updating a configuration twice in the same slot keeps only the last value:
`update (update w i y) i z = update w i z`. -/
theorem update_update_same {ι : Type*} [DecidableEq ι] {E : Type*} (w : ι → E) (i : ι) (y z : E) :
    Function.update (Function.update w i y) i z = Function.update w i z :=
  Function.update_idem y z w

/-- **The box projection `P = boxPInd` is independent of the slot-`i` coordinate on the
box**: for `y, y' ∈ A` the configurations `x_{i←y}`, `x_{i←y'}` give the same value (the
inner mean `∫_{z ∈ A}Φ(x_{i←z})` forgets `x i`, and both indicators are `1`). -/
theorem boxPInd_update_eq_of_mem {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} (volA : ℝ)
    {i : Fin N} {Φ : X N → ℝ} {x : X N} {y y' : EuclideanSpace ℝ (Fin 3)}
    (hy : y ∈ A) (hy' : y' ∈ A) :
    Work.UBBInputs8.boxPInd volA A i Φ (Function.update x i y)
      = Work.UBBInputs8.boxPInd volA A i Φ (Function.update x i y') := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin 3) =>
        Φ (Function.update (Function.update x i y) i z))
      = (fun z : EuclideanSpace ℝ (Fin 3) =>
        Φ (Function.update (Function.update x i y') i z)) := by
    funext z
    rw [update_update_same x i y z, update_update_same x i y' z]
  simp only [Work.UBBInputs8.boxPInd, Function.update_self]
  rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy', hfun]

/-- **The inner mean of a projection forgets the other coordinates**: if `u` and `u'` agree
outside slot `i`, then the box means `∫_{z ∈ A}Φ(u_{i←z})` and `∫_{z ∈ A}Φ(u'_{i←z})` agree.
This is the invariance behind the flat-part identities (both for the one-body term and,
iterated, for the pair term). -/
theorem boxPInd_inner_eq_of_agree {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))} {i : Fin N}
    {Φ : X N → ℝ} {u u' : X N} (h : ∀ k, k ≠ i → u k = u' k) :
    (∫ z in A, Φ (Function.update u i z)) = (∫ z in A, Φ (Function.update u' i z)) := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin 3) => Φ (Function.update u i z))
      = fun z => Φ (Function.update u' i z) := by
    funext z
    congr 1
    funext k
    by_cases hk : k = i
    · subst hk; simp [Function.update_self]
    · simp [Function.update_of_ne hk, h k hk]
  rw [hfun]

/-- **The double inner mean forgets everything outside the two updated slots**: for distinct
slots `i ≠ j`, if `x` and `x'` agree outside `{i, j}`, the iterated box means
`∫_ζ ∫_η Φ(x_{i←η, j←ζ})` agree.  This is the pair-companion (`boxPInd_pair_factor`) of the
flat-part identity: with it, `(P_iP_jΦ)(x) = (the double mean)·1_A(x_i)·1_A(x_j)` is invariant
on the box. -/
theorem boxPInd_pair_inner_eq_of_agree {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {i j : Fin N} (hij : i ≠ j) {Φ : X N → ℝ} {x x' : X N}
    (h : ∀ k, k ≠ i → k ≠ j → x k = x' k) (η : EuclideanSpace ℝ (Fin 3)) :
    (∫ ζ in A, Φ (Function.update (Function.update x i η) j ζ))
      = (∫ ζ in A, Φ (Function.update (Function.update x' i η) j ζ)) := by
  refine boxPInd_inner_eq_of_agree (i := j) (u := Function.update x i η)
    (u' := Function.update x' i η) ?_
  intro k hk
  by_cases hki : k = i
  · subst hki; simp [Function.update_self]
  · simp [Function.update_of_ne hki, h k hki hk]

/-- **The two peeled configurations agree outside the two updated slots**: for distinct slots
`i` and `j = i.succAbove j'` of an `(p+2)`-particle configuration,
`kcInsN (p+1) i (y, kcInsN p j' (z, r2))` and `kcInsN (p+1) i (0, kcInsN p j' (0, r2))` agree at
every slot other than `i` and `i.succAbove j'`.  This is the coordinate bookkeeping of the
double peel `abox_integral_peel2`, done by the finite case split on the two slot levels
(`Fin.exists_succAbove_eq` + the corpus's `kc_insN_apply_same` / `kc_insN_apply_succ`). -/
theorem kcInsN_pair_agree {p : ℕ} (i : Fin (p + 2)) (j' : Fin (p + 1))
    (y z : EuclideanSpace ℝ (Fin 3)) (r2 : X p) {k : Fin (p + 2)}
    (hk : k ≠ i) (hk' : k ≠ i.succAbove j') :
    (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) k
      = (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) k := by
  obtain ⟨k', rfl⟩ := Fin.exists_succAbove_eq hk
  rw [Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ]
  by_cases hk'' : k' = j'
  · subst hk''
    exact (hk' rfl).elim
  · obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (n := p) hk''
    rw [Submission.BoseGases.kc_insN_apply_succ, Submission.BoseGases.kc_insN_apply_succ]

/-- **Projection value of `P_i P_{i.succAbove j'}` at the peeled configuration.**  At
`x₀ = kcInsN (p+1) i (y, kcInsN p j' (z, r2))` the two projections unfold to the constant
`(1/volA)²·(double box mean of Φ at the zeroed configuration)` times the two indicators
`1_A(y)·1_A(z)`: the `η`-integrand is constant in `y` (both `Function.update`s overwrite the
two slots `i`, `i.succAbove j'`), which is `boxPInd_inner_eq_of_agree` at
`u := update x₀ i η`, `u' := update W₀ i η` with the pointwise hypothesis discharged by
`kcInsN_pair_agree`. -/
theorem boxPInd_pair_value {p : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) (volA : ℝ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) {Φ : X (p + 2) → ℝ}
    (y z : EuclideanSpace ℝ (Fin 3)) (r2 : X p) :
    Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
        (kcInsN (p + 1) i (y, kcInsN p j' (z, r2)))
      = (1 / volA) ^ 2 *
          (∫ η in dlBox ℓ d u, ∫ ζ in dlBox ℓ d u,
            Φ (Function.update (Function.update (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) i η)
                 (i.succAbove j') ζ))
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
  have hyi : (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i = y :=
    Submission.BoseGases.kc_insN_apply_same (p + 1) i y (kcInsN p j' (z, r2))
  have hzj : (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) (i.succAbove j') = z := by
    rw [Submission.BoseGases.kc_insN_apply_succ]
    exact Submission.BoseGases.kc_insN_apply_same p j' z r2
  have hne : i.succAbove j' ≠ i := Fin.succAbove_ne i j'
  have hinner : ∀ η : EuclideanSpace ℝ (Fin 3),
      (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
          (Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η)
        = (1 / volA) * (∫ ζ in dlBox ℓ d u,
            Φ (Function.update
              (Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η)
              (i.succAbove j') ζ))
          * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
    intro η
    simp only [Work.UBBInputs8.boxPInd]
    rw [Function.update_of_ne hne, hzj]
  have houter : Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
        (kcInsN (p + 1) i (y, kcInsN p j' (z, r2)))
      = (1 / volA) * (∫ η in dlBox ℓ d u,
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
            (Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η))
        * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y := by
    simp only [Work.UBBInputs8.boxPInd]
    rw [hyi]
  have hstep : (∫ η in dlBox ℓ d u,
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
          (Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η))
      = (∫ η in dlBox ℓ d u, (1 / volA) * (∫ ζ in dlBox ℓ d u,
            Φ (Function.update
              (Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η)
              (i.succAbove j') ζ)))
          * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z := by
    rw [← MeasureTheory.integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => hinner η)
  have hmean : (∫ η in dlBox ℓ d u, (1 / volA) * (∫ ζ in dlBox ℓ d u,
        Φ (Function.update
          (Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η)
          (i.succAbove j') ζ)))
      = (∫ η in dlBox ℓ d u, (1 / volA) * (∫ ζ in dlBox ℓ d u,
        Φ (Function.update
          (Function.update (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) i η)
          (i.succAbove j') ζ))) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    exact congrArg (fun t : ℝ => (1 / volA) * t)
      (boxPInd_inner_eq_of_agree (i := i.succAbove j')
        (u := Function.update (kcInsN (p + 1) i (y, kcInsN p j' (z, r2))) i η)
        (u' := Function.update (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) i η) (by
          intro k hk
          by_cases hki : k = i
          · subst hki
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hki, Function.update_of_ne hki,
              kcInsN_pair_agree i j' y z r2 hki hk]))
  rw [houter, hstep, hmean, MeasureTheory.integral_const_mul]
  ring

/-- **First move of `boxPInd_pair_factor`: the double peel of the pair integrand.**  Peel slot
`i : Fin (p+2)` and then the second peeled slot `j = i.succAbove j'` with
`abox_integral_peel2`, and reduce the two coordinate arguments of `w` down to the two peeled
variables `y` (slot `i`) and `z` (slot `i.succAbove j'`) using the corpus's
`kc_insN_apply_same` / `kc_insN_apply_succ`. -/
theorem boxPInd_pair_peel {p : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) (volA : ℝ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) {Φ : X (p + 2) → ℝ}
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt : IntegrableOn (fun x : X (p + 2) =>
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
          * w (x i) (x (i.succAbove j'))) (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
          * w (x i) (x (i.succAbove j')))
      = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
            (kcInsN (p + 1) i (y, kcInsN p j' (z, r2)))) ^ 2 * w y z := by
  have hpeel := Submission.BoseGases.abox_integral_peel2 (p := p) (ℓ := ℓ) i j'
    (fun x : X (p + 2) =>
      (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
        * w (x i) (x (i.succAbove j'))) hInt
  rw [hpeel]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [Submission.BoseGases.kc_insN_apply_same, Submission.BoseGases.kc_insN_apply_succ]

/-- **The box-mean flat-part identity at the localised kernels** (cleared form): for any
`volA`, any `F` and any slot `i` of an `N`-particle state,

    |A ∩ acube ℓ| · ∫_{abox N ℓ}(P_iΦ)²·F(x_i) = (∫_{A ∩ acube ℓ}F) · ∫_{abox N ℓ}(P_iΦ)² .

(Equivalently `∫(P_iΦ)²F(x_i) = ((∫_{A∩acube ℓ}F)/|A ∩ acube ℓ|)·‖P_iΦ‖²` when the
denominator is nonzero.)  It is this factorisation — the state-independent box mass times
the projected norm squared — that makes the mean-field square pay the `F`-weight. -/
theorem boxPInd_sq_mul_comp_localised {N : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    (volA : ℝ) (i : Fin N) {Φ : X N → ℝ} {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt : IntegrableOn
      (fun x : X N => (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i Φ x) ^ 2 * F (x i))
      (abox N ℓ) volume)
    (hIntP : IntegrableOn
      (fun x : X N => (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i Φ x) ^ 2)
      (abox N ℓ) volume) :
    (∫ z in dlBox ℓ d u ∩ acube ℓ, (1 : ℝ))
        * (∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i Φ x) ^ 2 * F (x i))
      = (∫ z in dlBox ℓ d u ∩ acube ℓ, F z)
        * (∫ x in abox N ℓ,
            (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i Φ x) ^ 2) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm⟩
  set A : Set (EuclideanSpace ℝ (Fin 3)) := dlBox ℓ d u with hAdef
  have hA : MeasurableSet A := Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  set c : X n → ℝ := fun r => (1 / volA) ^ 2 *
    (∫ z in A, Φ (Function.update (kcInsN n i (0, r)) i z)) ^ 2 with hcdef
  have hpeel1 : (∫ x in abox (n + 1) ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * F (x i))
      = ∫ r in abox n ℓ,
          (∫ y in acube ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))) ^ 2 * F y) := by
    rw [Submission.BoseGases.abox_integral_peel i _ hInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [Submission.BoseGases.kc_insN_apply_same]
  have hpeel2 : (∫ x in abox (n + 1) ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2)
      = ∫ r in abox n ℓ,
          (∫ y in acube ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))) ^ 2) :=
    Submission.BoseGases.abox_integral_peel i _ hIntP
  have hval : ∀ (r : X n) (y : EuclideanSpace ℝ (Fin 3)), y ∈ A →
      Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))
        = (1 / volA) * (∫ z in A, Φ (Function.update (kcInsN n i (0, r)) i z)) := by
    intro r y hy
    have hyi : (kcInsN n i (y, r)) i = y := Submission.BoseGases.kc_insN_apply_same n i y r
    have hfun : (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Function.update (kcInsN n i (y, r)) i z))
        = (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Function.update (kcInsN n i (0, r)) i z)) := by
      funext z
      rw [Submission.BoseGases.kcInsN_update_zero (n := n) (i := i) y r,
        update_update_same (kcInsN n i (0, r)) i y z]
    simp only [Work.UBBInputs8.boxPInd]
    rw [hyi, Set.indicator_of_mem hy, mul_one, hfun]
  have hzero : ∀ (r : X n) (y : EuclideanSpace ℝ (Fin 3)), y ∉ A →
      Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r)) = 0 := by
    intro r y hy
    have hyi : (kcInsN n i (y, r)) i = y := Submission.BoseGases.kc_insN_apply_same n i y r
    simp only [Work.UBBInputs8.boxPInd]
    rw [hyi, Set.indicator_of_notMem hy, mul_zero]
  have hinner1 : ∀ r : X n,
      (∫ y in acube ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))) ^ 2 * F y)
        = c r * (∫ y in A ∩ acube ℓ, F y) := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        (Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))) ^ 2 * F y
          = c r * ((A.indicator F) y) := by
      intro y
      by_cases hy : y ∈ A
      · rw [hval r y hy, Set.indicator_of_mem hy]
        simp only [hcdef]
        ring
      · rw [hzero r y hy, Set.indicator_of_notMem hy]
        ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_indicator (μ := volume.restrict (acube ℓ)) hA,
      Measure.restrict_restrict hA, Set.inter_comm]
  have hinner2 : ∀ r : X n,
      (∫ y in acube ℓ, (Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))) ^ 2)
        = c r * (∫ y in A ∩ acube ℓ, (1 : ℝ)) := by
    intro r
    have hpt : ∀ y : EuclideanSpace ℝ (Fin 3),
        (Work.UBBInputs8.boxPInd volA A i Φ (kcInsN n i (y, r))) ^ 2
          = c r * ((A.indicator (fun _ => (1 : ℝ))) y) := by
      intro y
      by_cases hy : y ∈ A
      · rw [hval r y hy, Set.indicator_of_mem hy]
        simp only [hcdef]
        ring
      · rw [hzero r y hy, Set.indicator_of_notMem hy]
        ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
      MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_indicator (μ := volume.restrict (acube ℓ)) hA,
      Measure.restrict_restrict hA, Set.inter_comm]
  rw [hpeel1, hpeel2]
  simp only [hinner1, hinner2]
  rw [MeasureTheory.integral_mul_const, MeasureTheory.integral_mul_const]
  ring

theorem boxPInd_pair_pull {p : ℕ} {ℓ d : ℝ} (u : EuclideanSpace ℝ (Fin 3)) (volA : ℝ)
    (i : Fin (p + 2)) (j' : Fin (p + 1)) {Φ : X (p + 2) → ℝ}
    {w : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hInt : IntegrableOn (fun x : X (p + 2) =>
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
          * w (x i) (x (i.succAbove j'))) (abox (p + 2) ℓ) volume) :
    (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
          * w (x i) (x (i.succAbove j')))
      = ∫ r2 in abox p ℓ, ((1 / volA) ^ 2 * (∫ η in dlBox ℓ d u, ∫ ζ in dlBox ℓ d u, Φ (Function.update (Function.update (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) i η) (i.succAbove j') ζ))) ^ 2
          * (∫ z in acube ℓ, ∫ y in acube ℓ,
              (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
                * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z * w y z) := by
  calc (∫ x in abox (p + 2) ℓ,
        (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ) x) ^ 2
          * w (x i) (x (i.succAbove j')))
      = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
          (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) i
            (Work.UBBInputs8.boxPInd volA (dlBox ℓ d u) (i.succAbove j') Φ)
            (kcInsN (p + 1) i (y, kcInsN p j' (z, r2)))) ^ 2 * w y z :=
        boxPInd_pair_peel (ℓ := ℓ) (d := d) (Φ := Φ) (w := w) u volA i j' hInt
    _ = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, ((1 / volA) ^ 2 * (∫ η in dlBox ℓ d u, ∫ ζ in dlBox ℓ d u, Φ (Function.update (Function.update (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) i η) (i.succAbove j') ζ))) ^ 2
          * ((dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
              * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z * w y z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        have h := boxPInd_pair_value (ℓ := ℓ) (d := d) (Φ := Φ) u volA i j' y z r2
        simp only [h]
        rcases em (y ∈ dlBox ℓ d u) with hy | hy
        · rcases em (z ∈ dlBox ℓ d u) with hz | hz
          · simp only [Set.indicator_of_mem hy, Set.indicator_of_mem hz]; ring
          · simp only [Set.indicator_of_mem hy, Set.indicator_of_notMem hz]; ring
        · rcases em (z ∈ dlBox ℓ d u) with hz | hz
          · simp only [Set.indicator_of_notMem hy, Set.indicator_of_mem hz]; ring
          · simp only [Set.indicator_of_notMem hy, Set.indicator_of_notMem hz]; ring
    _ = ∫ r2 in abox p ℓ, ((1 / volA) ^ 2 * (∫ η in dlBox ℓ d u, ∫ ζ in dlBox ℓ d u, Φ (Function.update (Function.update (kcInsN (p + 1) i (0, kcInsN p j' (0, r2))) i η) (i.succAbove j') ζ))) ^ 2
          * (∫ z in acube ℓ, ∫ y in acube ℓ,
              (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) y
                * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) z * w y z) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
        simp only [MeasureTheory.integral_const_mul]

/-! ## The `ĝω(0)`-slack: the Born-gap payment of the sharpened background

`PerBoxSectorBound`'s background coefficient `½ − c` (`c > 0`) is *larger in absolute value* than
FS's `½`; the difference `c·μ²·∬w_{1,B(u)}` is paid **only** by the `ĝω(0)`-slack
`∬w_{2,B} − ∬w_{1,B} ≥ 0` of the two-body kernel (this is the exact mechanism FS's proof has and
their *statement* discards; it is why the residual needs the strict Born gap
`Work.BoseFixB1B.int_v_gt_eight_pi_a`).  Concretely: the box `A₀`-main term carries the pair
coefficient `M₂ = ∬w_{2,B}` and the one-body coefficient `M₁ = ∬w_{1,B}`, and the slack
`(M₂ − M₁)(S² − S)/(2 volA²)` — which the corpus's `a0MainLocBox` *drops* (it is stated at
`D = 0`) — pays `c μ² M₁` as soon as `4c·M₁ ≤ M₂ − M₁`. -/

/-- **The `ĝω(0)`-slack pays the sharpened background** (pure real arithmetic).  Under the
Born-gap condition `4c·M₁ ≤ M₂ − M₁`, the smallness `μV ≥ 2` and the condensate-density lower
bound `μ ≤ S/V`, the box `A₀`-main term *with* the `(M₂ − M₁)`-slack dominates the FS remainder
main term read with the background coefficient `½ − c` in place of `½`. -/
lemma a0MainLocBox_slack_pays {V μ M1 M2 S c : ℝ} (hV : 0 < V) (hμ : 0 ≤ μ) (hM1 : 0 ≤ M1)
    (hM12 : M1 ≤ M2) (hc : 0 ≤ c) (hslack : 4 * c * M1 ≤ M2 - M1)
    (hu : μ ≤ S / V) (hμV : 2 ≤ μ * V) :
    (1 / 4) * (S / V - μ) ^ 2 * M1 - (1 / 2 - c) * μ ^ 2 * M1
        - (M1 / (2 * V)) * (2 * (S / V) + μ) - M1 / (4 * V ^ 2)
      ≤ Work.BoseFixB1.a0MainLocBox V μ M1 S
        + (M2 - M1) * (S ^ 2 - S) / (2 * V ^ 2) := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hid : (M2 - M1) * (S ^ 2 - S) / (2 * V ^ 2)
      = (M2 - M1) * ((S / V) * (S / V - 1 / V) / 2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hu0 : 0 ≤ S / V := le_trans hμ hu
  have hlow : μ / 2 ≤ S / V - 1 / V := by
    have h1 : 1 / V ≤ μ / 2 := by
      rw [div_le_iff₀ hV]
      linarith
    linarith
  have hprod : μ * (μ / 2) ≤ (S / V) * (S / V - 1 / V) :=
    mul_le_mul hu hlow (by linarith) hu0
  have hkey : c * μ ^ 2 * M1 ≤ (M2 - M1) * ((S / V) * (S / V - 1 / V) / 2) := by
    have h4 : 0 ≤ 4 * (c * M1) := by positivity
    have hb : (M2 - M1) * ((S / V) * (S / V - 1 / V) / 2)
        ≥ (4 * (c * M1)) * (μ * (μ / 2) / 2) := by
      refine mul_le_mul (by linarith [hslack]) (by linarith) (by positivity) (by linarith)
    nlinarith [hb, sq_nonneg μ, h4]
  have hglue : (1 / 4) * (S / V - μ) ^ 2 * M1 - (1 / 2 - c) * μ ^ 2 * M1
        - (M1 / (2 * V)) * (2 * (S / V) + μ) - M1 / (4 * V ^ 2)
      = Work.BoseFixB1.a0MainLocBox V μ M1 S + c * μ ^ 2 * M1 := by
    unfold Work.BoseFixB1.a0MainLocBox
    field_simp
    ring
  rw [hglue, hid]
  linarith [hkey]

/-- **The sharp `A₀` payment (session 4).**  This is the *pair-coefficient-sharp* companion of
`a0MainLocBox_slack_pays`, and it is the arithmetic core of the **dense (condensed) arm** of the
residual.  At the density `τ = S/V` the box `Q₀`-word satisfies

    boxQ0 ≥ (M₂/2)·(τ² − τ/V) − μ·τ·M₁      (`boxQ0_value` + `M₂ ≥ M₁` + `boxPairCount ≥ S² − S`),

so the residual's one-body line `c·μ·τ·M₁` plus the *sharpened* background `−(½−c)μ²M₁` are
dominated by the pair term as soon as

    (6c + c²)·M₁ ≤ (1 − 4c)·(M₂ − M₁)         (`4c`-form: Born gap `M₂ − M₁` beats `6c·M₁`),

because this is exactly `(1+c)²M₁ ≤ (1−4c)M₂`, i.e. the **negative discriminant** of

    (M₂/2)τ² − (1+c)μτM₁ + (½−2c)μ²M₁ ≥ 0     (for *every* τ ≥ 0).

The `V`-corrections (`τ/V`, `μ/V`, `1/V²`) are carried explicitly on the right; they are the
`n₀ ↔ n₀+1`/`S² − S` defects of `q0word_value`/`boxQ0_value`, and the caller pays them from the
uniform `μ²`-margin (needing only `μV ≳ 1`, FS's own regime).  The hypothesis `M₂ ≤ 2M₁` is FS
`eq:WSestimate` (`∫W₂ ≤ 2∫W₁`). -/
theorem a0Main_sharp_pays {M1 M2 μ c τ V : ℝ} (hM1 : 0 < M1) (hM12 : M1 ≤ M2)
    (hM2 : M2 ≤ 2 * M1) (hμ : 0 < μ) (hc : 0 < c) (hc4 : c < 1 / 4)
    (hβ : (6 * c + c ^ 2) * M1 ≤ (1 - 4 * c) * (M2 - M1)) (hV : 0 < V) (hτ : 0 ≤ τ) :
    (1 + c) * μ * τ * M1 - (1 / 2 - 2 * c) * μ ^ 2 * M1
      ≤ M2 / 2 * τ ^ 2 - M2 / 2 * (τ / V) + 2 * M1 * (τ / V + μ / V + 1 / V ^ 2) := by
  have hc4' : 0 < 1 - 4 * c := by linarith
  have hkey : (1 + c) ^ 2 * M1 ≤ (1 - 4 * c) * M2 := by nlinarith [hβ]
  have hdisc : ((1 + c) * μ * M1) ^ 2 ≤ 4 * (M2 / 2) * ((1 / 2 - 2 * c) * μ ^ 2 * M1) := by
    have hμ2 : 0 ≤ μ ^ 2 := sq_nonneg μ
    have hmul := mul_le_mul_of_nonneg_right hkey (mul_nonneg hμ2 hM1.le)
    nlinarith [hmul]
  have hQid : 4 * (M2 / 2) * (M2 / 2 * τ ^ 2 - ((1 + c) * μ * M1) * τ
        + (1 / 2 - 2 * c) * μ ^ 2 * M1)
      = (2 * (M2 / 2) * τ - (1 + c) * μ * M1) ^ 2
        + (4 * (M2 / 2) * ((1 / 2 - 2 * c) * μ ^ 2 * M1) - ((1 + c) * μ * M1) ^ 2) := by
    ring
  have hQ : 0 ≤ M2 / 2 * τ ^ 2 - ((1 + c) * μ * M1) * τ + (1 / 2 - 2 * c) * μ ^ 2 * M1 := by
    have hsq := sq_nonneg (2 * (M2 / 2) * τ - (1 + c) * μ * M1)
    nlinarith [hQid, hsq, hdisc, hM1, hM2]
  have hlin : 0 ≤ (2 * M1 - M2 / 2) * (τ / V) :=
    mul_nonneg (by linarith) (div_nonneg hτ hV.le)
  have hcst : 0 ≤ 2 * M1 * (μ / V + 1 / V ^ 2) := by positivity
  nlinarith [hQ, hlin, hcst]

/-- **The box `A₀`-main bound *with* the `ĝω(0)`-slack.**  This is
`Work.BoseFixB1.boxQ0_ge_a0MainBox` (PROVED) with the pair coefficient kept at the *two-body*
mass `M₂ = ∬w₂` instead of being replaced by the one-body mass `M₁ = ∬w₁`: the extra term
`(M₂ − M₁)(S² − S)/(2 volA²)` is exactly the `D`-slot of `Submission.BoseGases.a0_form_square_identity`
(`a0MainLocBox` is the `D = 0` instance).  The proof is the three-step chain of
`a0MainLocBox_le_counts` with the pair count `S² − S ≤ Pc` and the mass hierarchy `M₁ ≤ M₂` kept
at the *stronger* coefficient `(M₂ − M₁)`. -/
theorem boxQ0_ge_a0MainBox_slack {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        w2 p.1 p.2) ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hμ : 0 ≤ μ)
    (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ A w1)
    (hM2 : Work.BoseFixB1S.boxM1 ℓ A w1 ≤ Work.BoseFixB1S.boxM2 volA A w2)
    (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ)
    (hcS2 : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ) :
    Work.BoseFixB1.a0MainLocBox volA μ (Work.BoseFixB1S.boxM1 ℓ A w1)
        (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
      + (Work.BoseFixB1S.boxM2 volA A w2 - Work.BoseFixB1S.boxM1 ℓ A w1)
        * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
            - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
        / (2 * volA ^ 2)
      ≤ Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ := by
  set M1 : ℝ := Work.BoseFixB1S.boxM1 ℓ A w1 with hM1def
  set M2 : ℝ := Work.BoseFixB1S.boxM2 volA A w2 with hM2def
  set S : ℝ := Work.BoseFixB1S.boxFlatCount volA ℓ A Φ with hSdef
  set Pc : ℝ := Work.BoseFixB1S.boxPairCount volA ℓ A Φ with hPcdef
  have hQ0 := Work.BoseFixB1.boxQ0_value (N := N) (ℓ := ℓ) (volA := volA) (μ := μ) (A := A)
    (w1 := w1) (w2 := w2) (Φ := Φ) hℓ hvol hA hvolA hAc hw2i hfib hΦc
  have hcS2' : S ^ 2 - S ≤ Pc := by
    rw [hSdef, hPcdef]
    simpa only [sq] using hcS2
  have hcore := Work.BoseFixB1.a0MainLocBox_le_counts (V := volA) (μ := μ) (M1 := M1) (M2 := M1)
    (S := S) (Pc := Pc) hvol hμ hM1nn le_rfl hPcnn hcS2'
  have hsub : (M2 - M1) * (S ^ 2 - S) ≤ (M2 - M1) * Pc :=
    mul_le_mul_of_nonneg_left hcS2' (by rw [hM1def, hM2def]; linarith)
  have hstep : (M2 - M1) * (S ^ 2 - S) / (2 * volA ^ 2) ≤ (M2 - M1) * Pc / (2 * volA ^ 2) := by
    have hinv : (0 : ℝ) ≤ (2 * volA ^ 2)⁻¹ := by positivity
    have h := mul_le_mul_of_nonneg_right hsub hinv
    simpa only [div_eq_mul_inv] using h
  have hsum : (1 / 2) * (M1 / volA ^ 2) * Pc + (M2 - M1) * Pc / (2 * volA ^ 2)
      = (1 / 2) * (M2 / volA ^ 2) * Pc := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  have hQ0' : Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
      = (1 / 2) * (M2 / volA ^ 2) * Pc - μ * (M1 / volA) * S := hQ0
  linarith [hcore, hstep, hsum.le, hsum.ge, hQ0'.le, hQ0'.ge]

/-! ## The case split of the residual

The residual is split, exactly as in FS's own proof of `thm:smallbox`, on the size of the
**box-excited count** `n₊(B(u)) := Σᵢ∫(Q_{B(u),i}Φ)²` against the condensate count
`n·‖Φ‖²` (the convention of `Work.BoseFixB1S.perBoxMeanFieldB1`):

* **gap arm** (`n·‖Φ‖² ≤ n₊(B(u))`): the state is fully excited, `n₊ = n‖Φ‖²` and the
  *condensate* count `S = Σᵢ∫(P_{B(u),i}Φ)²` vanishes; here FS `eq:appgapestimate`
  (`sbKin ≥ c'²μ(a v)·n₊`, the *proved* `Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus`)
  together with the *uniform* fibre bound `|w₁-fibre| ≤ (ξ a v)·χ_{B(u)}` (the *proved*
  `Work.BoseFixB1S.PerBoxFibreB1`, consumed through
  `Work.BoseFixB1S.qLHSwordB_ge_neg_fibreUniform`) pays everything.  **This arm is proved
  below.**
* **flat arm** (`n₊(B(u)) < n·‖Φ‖²`): the condensate dominates; this is FS §5's mean-field
  analysis at the sliding box, and it is the one analytic residual left
  (`PerBoxSectorBoundFlat`, delegated).

The two arms merge by `min`/`max` of the thresholds/constants, using the monotonicity of the
mixture left-hand side in `c` (`mixLHS_mono_c`) and its antitonicity in `C`
(`mixLHS_anti_C`). -/

/-- **The mixture left-hand side of `PerBoxSectorBound`**, verbatim (without the leading
`∃ε₀ c C` and the `∀`-binder). -/
noncomputable abbrev mixLHS {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (c C μ : ℝ) (n : ℕ) (Φ : X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k *
      ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
        - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
            + μ * (_root_.BoseGases.a v)))

/-- The box-excited count `n₊(B(u)) = Σᵢ∫(Q_{B(u),i}Φ)²` of the state at the sliding box. -/
noncomputable abbrev boxNPlus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (n : ℕ)
    (Φ : X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (PBℓ v μ) (PBB v μ u)
    (Work.SmallBoxSliding.boxMass (PBℓ v μ) (PBd v μ) u) Φ

/-- **The gap arm** of the residual: `PerBoxSectorBound` restricted to the states whose
box-excited count dominates the condensate count `n‖Φ‖²`. -/
def PerBoxSectorBoundGap (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ interiorSet (PBℓ v μ) (PBd v μ) μ →
        (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) ≤ boxNPlus (v := v) μ n (Φ : X n → ℝ) u →
        mixLHS (v := v) h c C μ n (Φ : X n → ℝ) u ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)

/-- **The flat (condensed) arm** of the residual: `PerBoxSectorBound` restricted to the states
whose condensate count dominates the box-excited count — FS §5's mean-field regime. -/
def PerBoxSectorBoundFlat (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ interiorSet (PBℓ v μ) (PBd v μ) μ →
        boxNPlus (v := v) μ n (Φ : X n → ℝ) u < (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        mixLHS (v := v) h c C μ n (Φ : X n → ℝ) u ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)

/-! ### Monotonicity of the mixture left-hand side -/

/-- `mixLHS` is monotone in the `F`-coefficient `c`: writing
`(cF − (½−c)μ²) = c(F + μ²) − ½μ²`, the difference is `(c'−c)(F+μ²)W·m_k ≥ 0`. -/
theorem mixLHS_mono_c {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {c c' C μ : ℝ} {n : ℕ} {Φ : X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hcc : c ≤ c') (hμ : 0 < μ) (hW : 0 ≤ PBW h μ u) :
    mixLHS h c C μ n Φ u ≤ mixLHS h c' C μ n Φ u := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hm : 0 ≤ Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k :=
    Work.FockBridge.sectorMass_nonneg _ _ _ _
  have hV : 0 ≤ PBV v μ u := by
    rw [PBV, Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have ht : 0 ≤ (k : ℝ) / PBV v μ u := div_nonneg (Nat.cast_nonneg k) hV
  have hF : 0 ≤ psiWeight 1 μ ((k : ℝ) / PBV v μ u) := by
    rw [Work.SmallBoxSliding.psiWeight]
    have hd : 0 < 1 + (k : ℝ) / PBV v μ u * μ⁻¹ := by positivity
    positivity
  have hdiff : ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
        - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
            + μ * (_root_.BoseGases.a v)))
      ≤ ((c' * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c') * μ ^ 2) * PBW h μ u
        - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
            + μ * (_root_.BoseGases.a v))) := by
    set Fk : ℝ := psiWeight 1 μ ((k : ℝ) / PBV v μ u) with hFk
    set E : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
      + μ * (_root_.BoseGases.a v) with hE
    have hid : ((c' * Fk - (1 / 2 - c') * μ ^ 2) * PBW h μ u - C * E)
        - ((c * Fk - (1 / 2 - c) * μ ^ 2) * PBW h μ u - C * E)
        = (c' - c) * (Fk + μ ^ 2) * PBW h μ u := by ring
    have hprod : 0 ≤ (c' - c) * (Fk + μ ^ 2) * PBW h μ u := by
      have h1 : 0 ≤ c' - c := by linarith
      have h2 : 0 ≤ Fk := by rw [hFk]; exact hF
      exact mul_nonneg (mul_nonneg h1 (by positivity)) hW
    linarith [hid.le, hid.ge, hprod]
  exact mul_le_mul_of_nonneg_left hdiff hm

/-- `mixLHS` is antitone in the error constant `C`, since the error bracket
`μ²(a v)Γ·∬w₁ + μ(a v)` is nonnegative. -/
theorem mixLHS_anti_C {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {c C C' μ : ℝ} {n : ℕ} {Φ : X n → ℝ} {u : EuclideanSpace ℝ (Fin 3)}
    (hC : C ≤ C') (hμ : 0 < μ) (hav : 0 ≤ _root_.BoseGases.a v) (hW : 0 ≤ PBW h μ u)
    (hΓ : 0 ≤ PBΓ v μ) :
    mixLHS h c C' μ n Φ u ≤ mixLHS h c C μ n Φ u := by
  refine Finset.sum_le_sum fun k _ => ?_
  have hm : 0 ≤ Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k :=
    Work.FockBridge.sectorMass_nonneg _ _ _ _
  have hE : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
      + μ * (_root_.BoseGases.a v) := by positivity
  have hstep : C' * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
        + μ * (_root_.BoseGases.a v))
      ≥ C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
        + μ * (_root_.BoseGases.a v)) := by
    have := mul_le_mul_of_nonneg_right hC hE
    linarith
  have hdiff : ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
        - C' * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
            + μ * (_root_.BoseGases.a v)))
      ≤ ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
        - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
            + μ * (_root_.BoseGases.a v))) := by
    set Fk : ℝ := psiWeight 1 μ ((k : ℝ) / PBV v μ u) with hFk
    set E : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
      + μ * (_root_.BoseGases.a v) with hEdef
    have hid : ((c * Fk - (1 / 2 - c) * μ ^ 2) * PBW h μ u - C' * E)
        - ((c * Fk - (1 / 2 - c) * μ ^ 2) * PBW h μ u - C * E)
        = (C - C') * E := by ring
    have hprod : (C - C') * E ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hE
    linarith [hid.le, hid.ge, hprod]
  exact mul_le_mul_of_nonneg_left hdiff hm

/-- **The assembly**: the two arms imply the residual, with the common threshold
`min ε₀g ε₀f`, the common coefficient `min cg cf` and the common error constant `max Cg Cf`. -/
theorem perBoxSectorBound_of_arms {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hgap : PerBoxSectorBoundGap v h R) (hflat : PerBoxSectorBoundFlat v h R) :
    PerBoxSectorBound v h R := by
  obtain ⟨ε₀g, cg, Cg, hε₀g, hc0g, hc14g, hC0g, hg⟩ := hgap
  obtain ⟨ε₀f, cf, Cf, hε₀f, hc0f, hc14f, hC0f, hf⟩ := hflat
  refine ⟨min ε₀g ε₀f, min cg cf, max Cg Cf, lt_min hε₀g hε₀f, lt_min hc0g hc0f,
    le_trans (min_le_left _ _) hc14g, le_max_of_le_left hC0g, ?_⟩
  intro μ hAdm n Φ u hu
  have hAg : Adm v ε₀g μ := ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hAf : Adm v ε₀f μ := ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have hμ : 0 < μ := hAdm.1
  have hav : 0 ≤ _root_.BoseGases.a v := le_of_lt (Work.BoseFixB1.adm_a_pos hAdm)
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hW : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hΓ : 0 ≤ PBΓ v μ := by
    rw [PBΓ, Work.FockBridge.dlGamma]
    have h1 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have h2 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    exact mul_nonneg (pow_nonneg h1 3) (Real.rpow_nonneg h2 _)
  have hmono := mixLHS_mono_c (h := h) (c := min cg cf) (c' := cg) (C := max Cg Cf)
    (μ := μ) (n := n) (Φ := (Φ : X n → ℝ)) (u := u) (min_le_left _ _) hμ hW
  have hmonoC := mixLHS_anti_C (h := h) (c := cg) (C := Cg) (C' := max Cg Cf)
    (μ := μ) (n := n) (Φ := (Φ : X n → ℝ)) (u := u) (le_max_left _ _) hμ hav hW hΓ
  rcases lt_or_ge (boxNPlus (v := v) μ n (Φ : X n → ℝ) u)
      ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) with hlt | hle
  · have hmono2 := mixLHS_mono_c (h := h) (c := min cg cf) (c' := cf) (C := max Cg Cf)
      (μ := μ) (n := n) (Φ := (Φ : X n → ℝ)) (u := u) (min_le_right _ _) hμ hW
    have hmono2C := mixLHS_anti_C (h := h) (c := cf) (C := Cf) (C' := max Cg Cf)
      (μ := μ) (n := n) (Φ := (Φ : X n → ℝ)) (u := u) (le_max_right _ _) hμ hav hW hΓ
    exact le_trans (le_trans hmono2 hmono2C) (hf μ hAf n Φ u hu hlt)
  · exact le_trans (le_trans hmono hmonoC) (hg μ hAg n Φ u hu hle)

/-! ### The mixture left-hand side is dominated by the mean-field count term

The single technical observation that makes the whole residual *monotone in the count*: using the
linear bound `F(t) ≤ μ(t+μ)` (`psiWeight_one_le_mu_mul_add`) **before** discarding the background,
the `+μ²`-term it produces cancels the sharpened background exactly up to `(2c − ½)μ²W·‖Φ‖² ≤ 0`
(for `c ≤ 1/4`), leaving

    mixLHS h c C μ n Φ u  ≤  c·μ·(∬w₁/χ)·cnt ,      cnt := Σ_k k·m_k .

Consequently the residual is implied by the *count* inequality `c·μ·(∬w₁/χ)·cnt ≤ sbWord`
(with `c` the smaller of the two coefficients), and the gap/flat case split is only a convenient
way to prove that inequality (in the gap regime `cnt ≤ n‖Φ‖² ≤ n₊` bounds it by the gap payment
`sbKin ≥ c'²μ(a v)n₊`). -/

/-- The **mixture count** `cnt = Σ_k k·m_k` (the first moment of the `B(u)`-occupancy
distribution; it equals `⟨n_{B(u)}⟩` and also `boxFlatCount + boxQCount`). -/
noncomputable abbrev mixCnt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (n : ℕ)
    (Φ : X n → ℝ) (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) Φ k * (k : ℝ)

theorem mixLHS_le_muWcnt {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {c C μ : ℝ} {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    {u : EuclideanSpace ℝ (Fin 3)}
    (hc : c ≤ 1 / 4) (hc0 : 0 ≤ c) (hC : 0 ≤ C) (hμ : 0 < μ) (hW : 0 ≤ PBW h μ u)
    (hav : 0 ≤ _root_.BoseGases.a v) (hΓ : 0 ≤ PBΓ v μ) :
    mixLHS h c C μ n (Φ : X n → ℝ) u
      ≤ c * μ * (PBW h μ u / PBV v μ u) * mixCnt (v := v) μ n (Φ : X n → ℝ) u := by
  set E : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
    + μ * (_root_.BoseGases.a v) with hEdef
  have hE0 : 0 ≤ E := by
    rw [hEdef]; positivity
  set N : ℝ := Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; exact Work.BoseFixB1.normB_nonneg _
  set cnt : ℝ := mixCnt (v := v) μ n (Φ : X n → ℝ) u with hcntdef
  have hsum_m : (∑ k ∈ Finset.range (n + 1),
      Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k) = N := by
    rw [hNdef]; exact sectorMass_sum Φ u
  -- the exact unfolding
  have hmix : mixLHS h c C μ n (Φ : X n → ℝ) u
      = c * PBW h μ u * (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N := by
    have hpt : ∀ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
          * ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v)))
        = c * PBW h μ u * (Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
          - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E)
            * Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k := by
      intro k _; rw [hEdef]; ring
    rw [mixLHS, Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.mul_sum]
    · rw [← Finset.mul_sum, hsum_m]
  -- the `F`-sum in count form
  have hFs : (∑ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
          * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
      ≤ μ * (cnt / PBV v μ u + μ * N) := by
    have h1 := fWeight_sum_le (v := v) (μ := μ) hμ Φ u
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hμ.le)
    have hpt2 : ∀ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u + μ)
        = Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * ((k : ℝ) / PBV v μ u)
          + Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * μ := by
      intro k _; ring
    have h3 : (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u)) = cnt / PBV v μ u := by
      rw [hcntdef, mixCnt, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl hpt2, Finset.sum_add_distrib, ← Finset.sum_mul, hsum_m, h3]
    linarith [hN0, hμ]
  -- combine
  have hmul := mul_le_mul_of_nonneg_left hFs (mul_nonneg hc0 hW)
  have hid : c * PBW h μ u * (μ * (cnt / PBV v μ u + μ * N)) - ((1 / 2 - c) * μ ^ 2 * PBW h μ u
        + C * E) * N
      = c * μ * (PBW h μ u / PBV v μ u) * cnt
        + ((2 * c - 1 / 2) * μ ^ 2 * PBW h μ u * N - C * E * N) := by ring
  have hb1 : (2 * c - 1 / 2) * μ ^ 2 * PBW h μ u * N ≤ 0 := by
    have h1 : 2 * c - 1 / 2 ≤ 0 := by linarith
    have h2 : 0 ≤ μ ^ 2 * PBW h μ u * N := by positivity
    nlinarith [h1, h2]
  have hb2 : 0 ≤ C * E * N := by positivity
  have hmain : mixLHS h c C μ n (Φ : X n → ℝ) u
      ≤ c * μ * (PBW h μ u / PBV v μ u) * cnt := by
    rw [hmix]
    have hle : c * PBW h μ u * (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N
        ≤ c * PBW h μ u * (μ * (cnt / PBV v μ u + μ * N))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N := sub_le_sub_right hmul _
    rw [hid] at hle
    linarith [hle, hb1, hb2]
  simpa only [hcntdef] using hmain

/-! ### The gap arm (proved) -/

/-- **The gap arm holds.**  On `n‖Φ‖² ≤ n₊(B(u))` the whole left-hand side is paid by
`sbKin ≥ c'²μ(a v)·n₊` together with the *uniform* fibre bound
`|w₁-fibre| ≤ (ξ a v)χ_{B(u)}`, with `c := 1/4` and `C := 0`.

The `F`-weight is handled by the *linear* bound `F(t) ≤ μ(t+μ)` (`psiWeight_one_le_mu_mul_add`,
landed above): with `c = 1/4` the background terms cancel exactly
(`(1/4)F(t) − (1/4)μ² ≤ (1/4)μt`), the count `Σ_k k m_k ≤ n‖Φ‖²` turns the remainder into
`(1/4)μ(∬w₁/χ)‖Φ‖²`, and `∬w₁/χ ≤ C_W(a v)` (the proved mass law
`Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`) plus `n‖Φ‖² ≤ n₊` finish it. -/
theorem perBoxSectorBound_gap {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    PerBoxSectorBoundGap v h R := by
  obtain ⟨εw, C_W, hεw, hCW0, hWb⟩ :=
    Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime (v := v) (h := h) hv hvrad hR hv_supp
  obtain ⟨εf, ξ, hεf, hξ0, hfib⟩ :=
    Work.BoseFixB1S.PerBoxFibreB1 (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  set D : ℝ := Submission.BoseGases.chiSupAbs
    * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue with hDdef
  have hD0 : 0 ≤ D := mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
    (Submission.BoseGases.chiSmallDecay_nonneg Work.BoseBox.mValue)
  set CW : ℝ := max C_W 1 with hCWdef
  have hCW1 : 1 ≤ CW := le_max_right _ _
  have hCWpos : 0 < CW := lt_of_lt_of_le one_pos hCW1
  set c' : ℝ := Real.sqrt (ξ * D + CW / 4 + 1) with hc'def
  have hc'arg : 0 ≤ ξ * D + CW / 4 + 1 := by positivity
  have hc'sq : c' ^ 2 = ξ * D + CW / 4 + 1 := by
    rw [hc'def, Real.sq_sqrt hc'arg]
  have hc'0 : 0 < c' := Real.sqrt_pos.mpr (by positivity)
  have hkey : CW / 4 ≤ c' ^ 2 - ξ * D := by linarith [hc'sq]
  obtain ⟨εg, hεg, hregg⟩ :=
    Work.BoseFixB1.gapRegime_of_adm (v := v) hav (c' := c') hc'0.le
  refine ⟨min (min εw εf) (min εr εg), 1 / 4, 0, ?_, by norm_num, le_refl _, le_refl _, ?_⟩
  · exact lt_min (lt_min hεw hεf) (lt_min hεr hεg)
  intro μ hAdm n Φ u hu hgap
  have hmA : μ * (_root_.BoseGases.a v) ^ 3 ≤ min (min εw εf) (min εr εg) := hAdm.2.1
  have hAw : Adm v εw μ :=
    ⟨hAdm.1, le_trans (le_trans hmA (min_le_left _ _)) (min_le_left _ _), hAdm.2.2⟩
  have hAf : Adm v εf μ :=
    ⟨hAdm.1, le_trans (le_trans hmA (min_le_left _ _)) (min_le_right _ _), hAdm.2.2⟩
  have hAr : Adm v εr μ :=
    ⟨hAdm.1, le_trans (le_trans hmA (min_le_right _ _)) (min_le_left _ _), hAdm.2.2⟩
  have hAg : Adm v εg μ :=
    ⟨hAdm.1, le_trans (le_trans hmA (min_le_right _ _)) (min_le_right _ _), hAdm.2.2⟩
  have hμ : 0 < μ := hAdm.1
  have hav0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (le_trans (le_trans hmA (min_le_right _ _)) (min_le_left _ _))
  -- ### 1. the two mains
  have hVpre : 0 ≤ PBV v μ u := by
    rw [PBV, Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have hWle : PBW h μ u ≤ CW * (_root_.BoseGases.a v) * PBV v μ u := by
    have h1 := hWb μ hAw u
    have h2 : C_W * (_root_.BoseGases.a v) * PBV v μ u
        ≤ CW * (_root_.BoseGases.a v) * PBV v μ u := by
      have hCWle : C_W ≤ CW := le_max_left _ _
      have ha0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
      have h1 : C_W * (_root_.BoseGases.a v) ≤ CW * (_root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_right hCWle ha0
      exact mul_le_mul_of_nonneg_right h1 hVpre
    simpa only [PBW, PBV] using le_trans h1 h2
  -- ### 2. the fibre line
  have hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M :=
    one_le_PBM v μ
  have hΦc : Continuous (Φ : X n → ℝ) := Φ.contDiff.continuous
  have hql : -(ξ * D * μ * (_root_.BoseGases.a v)) * (n : ℝ)
        * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      ≤ Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) := by
    have hres := Work.BoseFixB1S.qLHSwordB_ge_neg_fibreUniform (v := v) h hv hv1 hR hv_supp
      hM1 hℓ hd hμ hav hξ0 hR16 hRχ (Φ : X n → ℝ) hΦc u (hfib μ hAf u)
    have heq : -(ξ * D * μ * (_root_.BoseGases.a v)) * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
        = -(ξ * _root_.BoseGases.a v * μ)
            * (Submission.BoseGases.chiSupAbs
                * Submission.BoseGases.chiSmallDecay
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
            * (n : ℝ)
            * (∫ x in Submission.BoseGases.abox n (PBℓ v μ), (Φ x) ^ 2) := by
      have hM : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M = Work.BoseBox.mValue := rfl
      simp only [hDdef, hM, Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
      ring
    rw [heq]
    simpa only [Work.BoseFixB1.sbPot, Work.BoseFixB1B.PBM, Work.BoseFixB1B.PBℓ,
      Work.BoseFixB1B.PBd, Work.BoseBoxFix.normB] using hres
  -- ### 3. the gap line
  have hsbkin : c' ^ 2 * μ * (_root_.BoseGases.a v) * boxNPlus (v := v) μ n (Φ : X n → ℝ) u
      ≤ Work.BoseFixB1.sbKin (v := v) μ
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u (Φ : X n → ℝ) := by
    have hres := Work.BoseFixB1.sbKin_ge_mu_av_cnPlus (v := v) (μ := μ) (c' := c')
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) (u := u) (n := n)
      (Φ : X n → ℝ) hav0 hμ.le hc'0.le (mul_pos hd hℓ)
      (Work.BoseFixB1.adm_eT_pos hAdm) (hregg μ hAg)
      (Work.BoseFixB1.tBwordKinInd_nonneg (Φ : X n → ℝ))
    simpa only [boxNPlus, Work.BoseFixB1.sbKin, Work.BoseFixB1B.PBℓ, Work.BoseFixB1B.PBd,
      Work.BoseFixB1B.PBM] using hres
  -- ### 4. the arithmetic
  have hW0 : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hV0 : 0 ≤ PBV v μ u := by
    rw [PBV, Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hQ0 : 0 ≤ boxNPlus (v := v) μ n (Φ : X n → ℝ) u := by
    rw [boxNPlus, Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hsum_m : (∑ k ∈ Finset.range (n + 1),
      Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k)
      = Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := sectorMass_sum Φ u
  have hsum_k : (∑ k ∈ Finset.range (n + 1),
      Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (k : ℝ))
      ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    calc (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (k : ℝ))
        ≤ ∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (n : ℝ) :=
          Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
            (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk))
            (Work.FockBridge.sectorMass_nonneg _ _ _ _)
      _ = (n : ℝ) * (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by rw [hsum_m]
  -- the `F`-weight sum, via `F(t) ≤ μ(t+μ)` and the first moment bound
  have hFs : (∑ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
          * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
      ≤ μ * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) / PBV v μ u
          + μ * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by
    have h1 := fWeight_sum_le (v := v) (μ := μ) hμ Φ u
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hμ.le)
    have hpt2 : ∀ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u + μ)
        = Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * ((k : ℝ) / PBV v μ u)
          + Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * μ := by
      intro k _; ring
    have h2 : (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u + μ))
        = (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * ((k : ℝ) / PBV v μ u))
          + μ * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
      rw [Finset.sum_congr rfl hpt2, Finset.sum_add_distrib, ← Finset.sum_mul, hsum_m]
      ring
    rw [h2]
    have h3 : (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u))
        = (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (k : ℝ))
          / PBV v μ u := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h3]
    have h4 : (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (k : ℝ))
          / PBV v μ u
        ≤ ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) / PBV v μ u :=
      mul_le_mul_of_nonneg_right hsum_k (inv_nonneg.mpr hV0)
    linarith [h4]
  -- the mixture identity at `c = 1/4`, `C = 0`
  have hmixid : mixLHS h (1 / 4) 0 μ n (Φ : X n → ℝ) u
      = (1 / 4) * PBW h μ u * (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
        - (1 / 4) * μ ^ 2 * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    have hpt : ∀ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
          * (((1 / 4) * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - 1 / 4) * μ ^ 2)
              * PBW h μ u
            - 0 * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v)))
        = (1 / 4) * PBW h μ u * (Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u)
              (Φ : X n → ℝ) k * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
          - (1 / 4) * μ ^ 2 * PBW h μ u
              * Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k := by
      intro k _
      have h14 : (1 / 2 - 1 / 4 : ℝ) = 1 / 4 := by norm_num
      rw [h14]; ring_nf
    rw [mixLHS, Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.mul_sum]
    · rw [← Finset.mul_sum, hsum_m]
  -- `∬w₁ / χ ≤ CW·(a v)`
  have hB : PBW h μ u / PBV v μ u ≤ CW * (_root_.BoseGases.a v) := by
    have hVinv0 : 0 ≤ (PBV v μ u)⁻¹ := inv_nonneg.mpr hV0
    have hVV : PBV v μ u * (PBV v μ u)⁻¹ ≤ 1 := by
      rcases eq_or_lt_of_le hV0 with h | h
      · rw [← h, inv_zero, mul_zero]; norm_num
      · rw [mul_inv_cancel₀ (ne_of_gt h)]
    calc PBW h μ u / PBV v μ u = PBW h μ u * (PBV v μ u)⁻¹ := rfl
      _ ≤ (CW * (_root_.BoseGases.a v) * PBV v μ u) * (PBV v μ u)⁻¹ :=
          mul_le_mul_of_nonneg_right hWle hVinv0
      _ = CW * (_root_.BoseGases.a v) * (PBV v μ u * (PBV v μ u)⁻¹) := by ring
      _ ≤ CW * (_root_.BoseGases.a v) * 1 :=
          mul_le_mul_of_nonneg_left hVV (by positivity)
      _ = CW * (_root_.BoseGases.a v) := by ring
  have hLHS_le : mixLHS h (1 / 4) 0 μ n (Φ : X n → ℝ) u
      ≤ (CW / 4) * (_root_.BoseGases.a v) * μ * boxNPlus (v := v) μ n (Φ : X n → ℝ) u := by
    rw [hmixid]
    have hstep1 : (1 / 4) * PBW h μ u * (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
        - (1 / 4) * μ ^ 2 * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
        ≤ (1 / 4) * μ * (PBW h μ u / PBV v μ u)
            * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by
      have hmul := mul_le_mul_of_nonneg_left hFs (by positivity : (0:ℝ) ≤ (1 / 4) * PBW h μ u)
      have hid : (1 / 4) * PBW h μ u * (μ * ((n : ℝ) * Work.BoseBoxFix.normB v μ n
              (Φ : X n → ℝ) / PBV v μ u + μ * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)))
            - (1 / 4) * μ ^ 2 * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
          = (1 / 4) * μ * (PBW h μ u / PBV v μ u)
            * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by ring
      linarith [hmul, hid.le, hid.ge]
    refine le_trans hstep1 ?_
    calc (1 / 4) * μ * (PBW h μ u / PBV v μ u)
          * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
        = (1 / 4) * μ * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
            * (PBW h μ u / PBV v μ u) := by ring
      _ ≤ (1 / 4) * μ * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
            * (CW * (_root_.BoseGases.a v)) := mul_le_mul_of_nonneg_left hB (by positivity)
      _ = (1 / 4) * μ * (CW * (_root_.BoseGases.a v))
            * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by ring
      _ ≤ (1 / 4) * μ * (CW * (_root_.BoseGases.a v)) * boxNPlus (v := v) μ n (Φ : X n → ℝ) u :=
          mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = (CW / 4) * (_root_.BoseGases.a v) * μ * boxNPlus (v := v) μ n (Φ : X n → ℝ) u := by ring
  have hRHS_ge : (CW / 4) * (_root_.BoseGases.a v) * μ * boxNPlus (v := v) μ n (Φ : X n → ℝ) u
      ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ) := by
    rw [Work.BoseFixB1.sbWord]
    have hD1 : (0:ℝ) ≤ ξ * D * μ * (_root_.BoseGases.a v) := by positivity
    have hmulq : ξ * D * μ * (_root_.BoseGases.a v) * ((n : ℝ) * Work.BoseBoxFix.normB
          v μ n (Φ : X n → ℝ))
        ≤ ξ * D * μ * (_root_.BoseGases.a v) * boxNPlus (v := v) μ n (Φ : X n → ℝ) u :=
      mul_le_mul_of_nonneg_left hgap hD1
    have hstep : (CW / 4) * (_root_.BoseGases.a v) * μ * boxNPlus (v := v) μ n (Φ : X n → ℝ) u
        ≤ c' ^ 2 * μ * (_root_.BoseGases.a v) * boxNPlus (v := v) μ n (Φ : X n → ℝ) u
          - ξ * D * μ * (_root_.BoseGases.a v)
            * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by
      have h1 : (CW / 4) * ((_root_.BoseGases.a v) * μ * boxNPlus (v := v) μ n (Φ : X n → ℝ) u)
          ≤ (c' ^ 2 - ξ * D) * ((_root_.BoseGases.a v) * μ
              * boxNPlus (v := v) μ n (Φ : X n → ℝ) u) :=
        mul_le_mul_of_nonneg_right hkey (by positivity)
      nlinarith [h1]
    linarith [hsbkin, hql, hstep]
  exact le_trans hLHS_le hRHS_ge

/-! ### The explicit fibre constant and the low-density arm of the residual

The residual is split again, this time on the balance between the sharpened background
`(½−2c)μ²(a v)χ·‖Φ‖²` collected from the `k=0` sectors and the two positive losses
(the `F`-weight on the occupied sectors and the fibre line of the potential word).  On the
**low-density side** the background dominates and the residual is a two-line consequence of
`mixLHS_le_muWcnt`, the uniform fibre bound `|fib| ≤ lowFibK·(a v)` (the *proved*
`Work.BoseFixB1.wSmall1Pair_fibre_abs_le`) and `0 ≤ tBwordBInd`.  The complement — the
*dense-box* regime `(½−2c)μχ‖Φ‖² < (c·∬w₁/χ + lowFibK·(a v))·n‖Φ‖²` — is the genuinely
restricted residual `PerBoxSectorBoundDense` below. -/

/-- The explicit uniform fibre constant of `Work.BoseFixB1.wSmall1Pair_fibre_abs_le` at FS's
regularity parameter `M = mValue`: `|w₁-fibre(z)| ≤ lowFibK·(a v)` for every `z`. -/
noncomputable def lowFibK : ℝ :=
  (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue)
    * ((2 * (Submission.BoseGases.chiSupAbs
          * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue)
        / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue) * (8 * Real.pi))

theorem lowFibK_nonneg : 0 ≤ lowFibK := by
  have hD0 : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmallDecay Work.BoseBox.mValue :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg _)
  have hS0 : 0 < Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue :=
    Work.SmallBoxSliding.smallConvLower_pos _
  rw [lowFibK]
  positivity

/-- **The uniform fibre bound at `lowFibK`** (`M = mValue` instance of
`Work.BoseFixB1.wSmall1Pair_fibre_abs_le`). -/
theorem fibre_abs_le_lowFibK {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R0 : ℝ} (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0)
    (hR0 : 0 < R0) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hR : R0 ≤ ℓ * d / 16)
    (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0) (u z : EuclideanSpace ℝ (Fin 3)) :
    |∫ y in Submission.BoseGases.acube ℓ,
        Submission.BoseGases.wSmallPair Work.BoseBox.mValue ℓ d u
          (Submission.BoseGases.g0 v h) z y| ≤ lowFibK * _root_.BoseGases.a v := by
  have hM : 1 ≤ Work.BoseBox.mValue := by rw [Work.BoseBox.mValue]; norm_num
  have h1 := Work.BoseFixB1.wSmall1Pair_fibre_abs_le (v := v) (h := h) (R0 := R0) hv_supp hR0
    hv hvrad hM hℓ hd hR hRχ u z
  rw [lowFibK]
  refine le_trans h1 (le_of_eq ?_)
  ring

/-- **The fibre line of the potential word is bounded below by `−lowFibK·(a v)·μ·n‖Φ‖²`.**  From
the exact split `sbPot = −μ·fibSum + pairSum` (`Work.BoseFixB1.sbPot_split`), the pointwise
nonnegativity of the pair kernel (`Work.BoseFixB1.perBoxMFCase_wSmallPair_nonneg`) and the
uniform fibre bound. -/
theorem sbPot_ge_neg_lowFibK {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {ε₀ μ : ℝ} (hAdm : Adm v ε₀ μ) (n : ℕ) (Φ : X n → ℝ) (hΦc : Continuous Φ)
    (u : EuclideanSpace ℝ (Fin 3)) (hR16 : R ≤ PBℓ v μ * PBd v μ / 16)
    (hRχ : R ≤ PBℓ v μ * Submission.BoseGases.chiR0) :
    -(μ * lowFibK * _root_.BoseGases.a v * (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ)
      ≤ Work.BoseFixB1.sbPot h μ u Φ := by
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ PBM v μ := one_le_PBM v μ
  have hsplit := Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
    hAdm hΦc u hR16 hRχ
  have hpair : 0 ≤ Work.BoseFixB1.pairSum v (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ := by
    rw [Work.BoseFixB1.pairSum]
    refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
    refine mul_nonneg (by norm_num) ?_
    refine Finset.sum_nonneg fun p _ => ?_
    exact Work.BoseFixB1.perBoxMFCase_wSmallPair_nonneg (M := PBM v μ) (ℓ := PBℓ v μ)
      (d := PBd v μ) (u := u) (x := x p.1) (y := x p.2) hv
  have hfib : Work.BoseFixB1.fibSum h (PBM v μ) (PBℓ v μ) (PBd v μ) u Φ
      ≤ lowFibK * _root_.BoseGases.a v * (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by
    have hInt := Work.BoseFixB1.integrableOn_fibSumIntegrand (v := v) (h := h) (R0 := R)
      hv_supp hR hv hvrad (M := PBM v μ) hM1 hℓ hd hR16 hRχ u hΦc
    rw [Work.BoseFixB1.fibSum]
    have hg : MeasureTheory.IntegrableOn (fun x : X n =>
        (Φ x) ^ 2 * ((n : ℝ) * (lowFibK * _root_.BoseGases.a v))) (abox n (PBℓ v μ)) :=
      ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
        (((hΦc.pow 2).mul continuous_const).continuousOn) 
    have hpt : ∀ x : X n, (Φ x) ^ 2 * (∑ i : Fin n, ∫ y in Submission.BoseGases.acube (PBℓ v μ),
          Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i) y)
        ≤ (Φ x) ^ 2 * ((n : ℝ) * (lowFibK * _root_.BoseGases.a v)) := by
      intro x
      have h1 : ∀ i : Fin n, (∫ y in Submission.BoseGases.acube (PBℓ v μ),
            Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i) y)
          ≤ lowFibK * _root_.BoseGases.a v := by
        intro i
        have := Work.BoseFixB1B.fibre_abs_le_lowFibK (v := v) (h := h) (R0 := R) hv_supp hR hv
          hvrad hℓ hd hR16 hRχ u (x i)
        exact le_trans (le_abs_self _) (by simpa only [Work.BoseFixB1B.PBM, Work.BoseFixB1B.PBℓ,
          Work.BoseFixB1B.PBd, Work.BoseFixB1.M_eq_mValue, Submission.BoseGases.w1Fibre,
          Submission.BoseGases.wSmall1Pair] using this)
      have h2 : (∑ i : Fin n, ∫ y in Submission.BoseGases.acube (PBℓ v μ),
            Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i) y)
          ≤ (n : ℝ) * (lowFibK * _root_.BoseGases.a v) := by
        calc (∑ i : Fin n, ∫ y in Submission.BoseGases.acube (PBℓ v μ),
              Submission.BoseGases.wSmall1Pair h (PBM v μ) (PBℓ v μ) (PBd v μ) u (x i) y)
            ≤ ∑ _i : Fin n, (lowFibK * _root_.BoseGases.a v) := Finset.sum_le_sum fun i _ => h1 i
          _ = (n : ℝ) * (lowFibK * _root_.BoseGases.a v) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have hmono := MeasureTheory.integral_mono_ae hInt hg (Filter.Eventually.of_forall hpt)
    have heq : (∫ x in abox n (PBℓ v μ),
          (Φ x) ^ 2 * ((n : ℝ) * (lowFibK * _root_.BoseGases.a v)))
        = lowFibK * _root_.BoseGases.a v * (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by
      rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, MeasureTheory.integral_mul_const]
      ring
    rw [heq] at hmono
    exact hmono
  have hmu := mul_le_mul_of_nonneg_left hfib (show (0:ℝ) ≤ μ from le_of_lt hAdm.1)
  linarith [hsplit.le, hsplit.ge, hpair, hmu]

/-- **The exposed mixture bound** (the intermediate step of `mixLHS_le_muWcnt`, kept): for
`c ≤ 1/4` and `C ≥ 0`,
`mixLHS h c C μ n Φ u ≤ c·μ·(∬w₁/χ)·cnt − (½−2c)·μ²·∬w₁·‖Φ‖²`. -/
theorem mixLHS_le_muWcnt_sub {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {c C μ : ℝ} {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
    {u : EuclideanSpace ℝ (Fin 3)}
    (hc : c ≤ 1 / 4) (hc0 : 0 ≤ c) (hC : 0 ≤ C) (hμ : 0 < μ) (hW : 0 ≤ PBW h μ u)
    (hav : 0 ≤ _root_.BoseGases.a v) (hΓ : 0 ≤ PBΓ v μ) :
    mixLHS h c C μ n (Φ : X n → ℝ) u
      ≤ c * μ * (PBW h μ u / PBV v μ u) * mixCnt (v := v) μ n (Φ : X n → ℝ) u
        - (1 / 2 - 2 * c) * μ ^ 2 * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
  set E : ℝ := μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
    + μ * (_root_.BoseGases.a v) with hEdef
  have hE0 : 0 ≤ E := by rw [hEdef]; positivity
  set N : ℝ := Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) with hNdef
  have hN0 : 0 ≤ N := by rw [hNdef]; exact Work.BoseFixB1.normB_nonneg _
  set cnt : ℝ := mixCnt (v := v) μ n (Φ : X n → ℝ) u with hcntdef
  have hsum_m : (∑ k ∈ Finset.range (n + 1),
      Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k) = N := by
    rw [hNdef]; exact sectorMass_sum Φ u
  have hmix : mixLHS h c C μ n (Φ : X n → ℝ) u
      = c * PBW h μ u * (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N := by
    have hpt : ∀ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
          * ((c * psiWeight 1 μ ((k : ℝ) / PBV v μ u) - (1 / 2 - c) * μ ^ 2) * PBW h μ u
            - C * (μ ^ 2 * (_root_.BoseGases.a v) * PBΓ v μ * PBW h μ u
                + μ * (_root_.BoseGases.a v)))
        = c * PBW h μ u * (Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
          - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E)
            * Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k := by
      intro k _; rw [hEdef]; ring
    rw [mixLHS, Finset.sum_congr rfl hpt, Finset.sum_sub_distrib]
    congr 1
    · rw [← Finset.mul_sum]
    · rw [← Finset.mul_sum, hsum_m]
  have hFs : (∑ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
          * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
      ≤ μ * (cnt / PBV v μ u + μ * N) := by
    have h1 := fWeight_sum_le (v := v) (μ := μ) hμ Φ u
    refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hμ.le)
    have hpt2 : ∀ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u + μ)
        = Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
              * ((k : ℝ) / PBV v μ u)
          + Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * μ := by
      intro k _; ring
    have h3 : (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * ((k : ℝ) / PBV v μ u)) = cnt / PBV v μ u := by
      rw [hcntdef, mixCnt, Finset.sum_div]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [Finset.sum_congr rfl hpt2, Finset.sum_add_distrib, ← Finset.sum_mul, hsum_m, h3]
    linarith [hN0, hμ]
  have hmul := mul_le_mul_of_nonneg_left hFs (mul_nonneg hc0 hW)
  have hid : c * PBW h μ u * (μ * (cnt / PBV v μ u + μ * N))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N
      = c * μ * (PBW h μ u / PBV v μ u) * cnt
        + ((2 * c - 1 / 2) * μ ^ 2 * PBW h μ u * N - C * E * N) := by ring
  have hCEN : 0 ≤ C * E * N := by positivity
  have hmain : mixLHS h c C μ n (Φ : X n → ℝ) u
      ≤ c * μ * (PBW h μ u / PBV v μ u) * cnt - (1 / 2 - 2 * c) * μ ^ 2 * PBW h μ u * N := by
    rw [hmix]
    have hle : c * PBW h μ u * (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k
            * psiWeight 1 μ ((k : ℝ) / PBV v μ u))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N
        ≤ c * PBW h μ u * (μ * (cnt / PBV v μ u + μ * N))
        - ((1 / 2 - c) * μ ^ 2 * PBW h μ u + C * E) * N := sub_le_sub_right hmul _
    rw [hid] at hle
    linarith [hle, hCEN]
  simpa only [hcntdef, hNdef] using hmain

/-- **The low-density arm of the residual.**  There is a threshold `ε₀` such that for every
admissible `μ`, every coefficient `0 < c ≤ 1/4`, every box state and every `u ∈ I₋` satisfying the
background-domination condition

`(½−2c)·μ²·∬w₁·‖Φ‖² ≥ (c·∬w₁/χ + lowFibK·(a v))·n·‖Φ‖²`

the residual holds with `C = 0`.  (The complement of this condition is the dense-box regime
`PerBoxSectorBoundDense`.) -/
theorem perBoxSectorBound_lowDensity {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ μ : ℝ, Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
          (u : EuclideanSpace ℝ (Fin 3)),
          u ∈ interiorSet (PBℓ v μ) (PBd v μ) μ →
          ∀ c : ℝ, 0 < c → c ≤ 1 / 4 →
          (1 / 2 - 2 * c) * μ * PBW h μ u
              * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
            ≥ (c * (PBW h μ u / PBV v μ u) + lowFibK * (_root_.BoseGases.a v))
              * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) →
          mixLHS h c 0 μ n (Φ : X n → ℝ) u ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ) := by
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨εr, hεr, ?_⟩
  intro μ hAdm n Φ u hu c hc0 hc14 hcond
  have hμ : 0 < μ := hAdm.1
  have hav0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ hAdm.2.1
  have hW : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hΓ : 0 ≤ PBΓ v μ := by
    rw [PBΓ, Work.FockBridge.dlGamma]
    have h1 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have h2 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    exact mul_nonneg (pow_nonneg h1 3) (Real.rpow_nonneg h2 _)
  have hN0 : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  have hcnt_le : mixCnt (v := v) μ n (Φ : X n → ℝ) u
      ≤ (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    have hsum_m := sectorMass_sum (v := v) (μ := μ) Φ u
    have hmain : (∑ k ∈ Finset.range (n + 1),
          Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (k : ℝ))
        ≤ (n : ℝ) * (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k) := by
      calc (∑ k ∈ Finset.range (n + 1),
            Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (k : ℝ))
          ≤ ∑ k ∈ Finset.range (n + 1),
              Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k * (n : ℝ) :=
            Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left
              (by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk))
              (Work.FockBridge.sectorMass_nonneg _ _ _ _)
        _ = (n : ℝ) * (∑ k ∈ Finset.range (n + 1),
              Work.FockBridge.sectorMass (PBℓ v μ) (PBB v μ u) (Φ : X n → ℝ) k) := by
            rw [← Finset.sum_mul]; ring
    rw [mixCnt, ← hsum_m]
    exact hmain
  have hmix := mixLHS_le_muWcnt_sub (v := v) (h := h) (c := c) (C := 0) (μ := μ) (n := n)
    Φ (u := u) hc14 hc0.le (le_refl 0) hμ hW hav0 hΓ
  have hsbkin : 0 ≤ Work.BoseFixB1.sbKin (v := v) μ (PBM v μ) u (Φ : X n → ℝ) := by
    rw [Work.BoseFixB1.sbKin]
    exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ (le_of_lt (Work.BoseFixB1.adm_eT_pos hAdm)) u _
  have hsbpot := sbPot_ge_neg_lowFibK (v := v) (h := h) (R := R) hv hv1 hvrad hR hv_supp hAdm
    n (Φ : X n → ℝ) Φ.contDiff.continuous u hR16 hRχ
  have hV0 : 0 ≤ PBV v μ u := by
    rw [PBV, Work.SmallBoxSliding.chiMass_def]
    exact integral_nonneg fun x => sq_nonneg _
  have hstep : c * μ * (PBW h μ u / PBV v μ u) * mixCnt (v := v) μ n (Φ : X n → ℝ) u
      ≤ (1 / 2 - 2 * c) * μ ^ 2 * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
        - μ * lowFibK * _root_.BoseGases.a v * (n : ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    have hcW0 : 0 ≤ c * (PBW h μ u / PBV v μ u) :=
      mul_nonneg hc0.le (div_nonneg hW hV0)
    have h1 : c * (PBW h μ u / PBV v μ u) * mixCnt (v := v) μ n (Φ : X n → ℝ) u
        ≤ c * (PBW h μ u / PBV v μ u) * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) :=
      mul_le_mul_of_nonneg_left hcnt_le hcW0
    have h2 : (c * (PBW h μ u / PBV v μ u) + lowFibK * (_root_.BoseGases.a v))
          * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
        ≤ (1 / 2 - 2 * c) * μ * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := hcond
    nlinarith [h1, h2, hμ.le]
  have hlow : mixLHS h c 0 μ n (Φ : X n → ℝ) u
      ≤ -(μ * lowFibK * _root_.BoseGases.a v * (n : ℝ)
          * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)) := by
    linarith [hmix, hstep]
  have hlow2 : mixLHS h c 0 μ n (Φ : X n → ℝ) u
      ≤ Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) := le_trans hlow hsbpot
  have hsbword : Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)
      = Work.BoseFixB1.sbKin (v := v) μ (PBM v μ) u (Φ : X n → ℝ)
        + Work.BoseFixB1.sbPot h μ u (Φ : X n → ℝ) := rfl
  rw [hsbword]
  linarith [hlow2, hsbkin]

/-- **The dense-box complement** of the residual: the same mixture inequality restricted to the
states whose box occupancy beats the background,

`(c·∬w₁/χ + lowFibK·(a v))·n‖Φ‖² > (½−2c)·μ²·∬w₁·‖Φ‖²`.

Together with `perBoxSectorBound_lowDensity` this covers every state, so this is the genuinely
restricted residual left by the low-density split. -/
def PerBoxSectorBoundDense (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (R : ℝ) : Prop :=
  ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ c ≤ 1 / 4 ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (PBℓ v μ))
        (u : EuclideanSpace ℝ (Fin 3)),
        u ∈ interiorSet (PBℓ v μ) (PBd v μ) μ →
        (c * (PBW h μ u / PBV v μ u) + lowFibK * (_root_.BoseGases.a v))
            * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
          > (1 / 2 - 2 * c) * μ * PBW h μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) →
        mixLHS h c C μ n (Φ : X n → ℝ) u ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)

/-- **The low-density arm and the dense arm cover the residual** (session 4).  The low arm
(`perBoxSectorBound_lowDensity`, PROVED, with `C := 0`) applies at the dense arm's coefficient `c`
(its own statement quantifies over every `0 < c ≤ 1/4`), and the case split is the dichotomy
`(c·∬w₁/χ + ξ(a v))·n‖Φ‖² ≤ (½−2c)μ·∬w₁·‖Φ‖²` (low) vs its strict complement (dense); the error
constant is then raised from `0` to `C` by the antitone monotonicity `mixLHS_anti_C`. -/
theorem perBoxSectorBound_of_lowDensity_dense {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hdense : PerBoxSectorBoundDense v h R) :
    PerBoxSectorBound v h R := by
  obtain ⟨ε₀d, cd, Cd, hεd, hcd0, hcd14, hCd0, hdense'⟩ := hdense
  obtain ⟨ε₀l, hεl, hlow'⟩ := perBoxSectorBound_lowDensity (v := v) h hv hv1 hvrad hR hv_supp hav
  refine ⟨min ε₀l ε₀d, cd, Cd, lt_min hεl hεd, hcd0, hcd14, hCd0, ?_⟩
  intro μ hAdm n Φ u hu
  have hAd : Adm v ε₀d μ := ⟨hAdm.1, le_trans hAdm.2.1 (min_le_right _ _), hAdm.2.2⟩
  have hAl : Adm v ε₀l μ := ⟨hAdm.1, le_trans hAdm.2.1 (min_le_left _ _), hAdm.2.2⟩
  have hμ : 0 < μ := hAdm.1
  have hav0 : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have hℓ : 0 < PBℓ v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < PBd v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hW : 0 ≤ PBW h μ u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hΓ : 0 ≤ PBΓ v μ := by
    rw [PBΓ, Work.FockBridge.dlGamma]
    have h1 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
      le_of_lt (Work.BoseFixB1.paramsAt_KB_pos hAdm)
    have h2 : 0 ≤ μ * (_root_.BoseGases.a v) ^ 3 := by positivity
    exact mul_nonneg (pow_nonneg h1 3) (Real.rpow_nonneg h2 _)
  rcases lt_or_ge ((1 / 2 - 2 * cd) * μ * PBW h μ u
        * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))
      ((cd * (PBW h μ u / PBV v μ u) + lowFibK * (_root_.BoseGases.a v))
        * ((n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ))) with hlt | hge
  · exact hdense' μ hAd n Φ u hu hlt
  · have hlow := hlow' μ hAl n Φ u hu cd hcd0 hcd14 hge
    exact le_trans (mixLHS_anti_C (h := h) (c := cd) (C := 0) (C' := Cd)
      (μ := μ) (n := n) (Φ := (Φ : X n → ℝ)) (u := u) hCd0 hμ hav0 hW hΓ) hlow

theorem perBoxSectorBound_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1B.PerBoxSectorBound v h R := by
  -- (session 5) The residual is FS `thm:smallbox` read at the counting operator `n_{B(u)}` of the
  -- sliding box.  The corpus's critical path proves it from the *termwise* (per-occupancy-sector)
  -- residual `Work.BoseFixB1.PerSectorBoundG`:
  --
  --   `PerBoxSectorBound`  ⟸  `PerBoxSectorBoundG`      (`perBoxSectorBound_of_G`, PROVED)
  --                        ⟸  `PerSectorBoundG`         (`perBoxSectorBoundG_of_pieces`, PROVED)
  --                              + `SbWordSectorAdditive` (`sbWordSectorAdditiveAdm`, PROVED)
  --                        ⟸  `PerSectorBoundG`         (the corpus's single named residual).
  --
  -- The two assembly lemmas and the sector additivity are sorry-free and axiom-clean
  -- (`#print axioms` = `[propext, Classical.choice, Quot.sound]`); the only non-proved input of
  -- this proof is `Work.BoseFixB1.perSectorBoundG_holds`, which sits in its own module.
  obtain ⟨ε₀a, hε₀a, hadd⟩ :=
    Work.BoseFixB1.sbWordSectorAdditiveAdm (v := v) h hv hv1 hvrad hR hv_supp hav
  exact perBoxSectorBound_of_G (v := v) (h := h) (R := R)
    (Work.BoseFixB1.perBoxSectorBoundG_of_pieces (v := v) (h := h) (R := R) hε₀a hadd
      (Work.BoseFixB1.perSectorBoundG_holds (v := v) h hv hv1 hvrad hR hv_supp hav))

end Work.BoseFixB1B

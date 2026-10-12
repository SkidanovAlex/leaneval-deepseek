import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1B.flatBranchMaxFreeDefs
import Submission.Work.BoseFixB1B.gapAtAll
import Submission.Work.LocRepoint.bandSet_measure_le_nohyp
import Submission.Work.LocRepoint.chiSmallB_sq_integral_u
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.PerBoxSmoothHolds` — Piece 1: FS `thm:smallbox` at the sliding box

Target (frozen, kept verbatim at the bottom of this file):

    theorem PerBoxSmoothHolds (v) (h : ScatSol v) (hv : 0 ≤ v) (hv1 : MemLp v 1)
      (hvrad : IsRadial v) {R} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball 0 R)
      (hav : 0 < a v) {J} (hJ : Work.UBB.lhyC ≤ J) : PerBoxSmooth v h R J

## SESSION FINDINGS (this file's session) — the reduction to the corpus's own branch split

`PerBoxSmooth v h R J`'s body is *the same inequality* as `Work.BoseFixB1.PerBoxF`, only with the
extra hypotheses `0 < μ`, `0 < normB`, `IsLowB v h J μ n Φ` and `u ∈ interiorSet` (⊆ `goodSet`):
`fWeight` is `W·∫Φ²F(t)`, `boxErrShape` is `PerBoxF`'s error bracket, and the two displays are
related by `ring` — see `perBoxF_to_smooth` below.  Hence

    PerBoxSmooth  ⟸  the `PerBoxF` conclusion on `goodSet`     (`perBoxSmoothHolds_of_goodSet`)

and the corpus's per-box chapter splits the latter (`Work.BoseFixB1`):

* **thin boxes** — PROVED (`Work.BoseFixB1.perBoxF_thin_holds`, `c₁ = 1/4`, `C = 0`);
* **gap branch** (`γ_gap·n·‖Φ‖² ≤ n₊(B)`) — PROVED
  (`Work.BoseFixB1.perBoxF_of_gapPayment`, `c₁ = 1/4`, explicit `γ_gap ≤ 10^{-100}`, `C = 1`);
* **flat branch** (`n₊(B) < γ₀·n·‖Φ‖²` on thick boxes) — **the remaining obligation**; delegated
  this session as `Work.BoseFixB1B.flatBranch` (`Submission/Work/BoseFixB1B/flatBranch.lean`),
  with its standalone combinatorial input (the ANOVA/Pythagoras inequality
  `∫_{Bⁿ}(Ψ − ⨍Ψ)² ≤ n₊(B)`) delegated as `Work.BoseFixB1B.fibreANOVA`
  (`Submission/Work/BoseFixB1B/fibreANOVA.lean`).

`perBoxF_of_branches` below assembles the two branches plus the thin case into the `PerBoxF`
conclusion on `goodSet`.  The two branches must meet at a *common* threshold: the proved
`perBoxF_of_gapPayment` produces only *some* `γ_gap`, so the gap side is consumed in the
strengthened form `Work.BoseFixB1B.gapAtAll` (**PROVED** this session,
`Submission/Work/BoseFixB1B/gapAtAll.lean`) — the re-run of the same proof with `c'` chosen from
the threshold, giving the gap branch at *every* prescribed `γ > 0`; the flat branch is then used at
its own `γ₀`.

## Delegation ledger of the flat branch (the single remaining obligation)

The flat branch's route and quantitative facts are recorded in
`Submission/Work/BoseFixB1B/FINDING_flatBranch_route.md` (written by the holder of
`flatBranch.lean`).  Its blockers are delegated this session:

| piece | content | path |
|---|---|---|
| `fibreANOVA` | the ANOVA/Pythagoras inequality `∫_{Bⁿ}(Ψ − ⨍Ψ)² ≤ n₊(B)` — the standalone combinatorial input | `BoseFixB1B/fibreANOVA.lean` |
| `conv3SmallLowerFlat` | the *sharp* uniform lower bound `c ≤ conv3Small mValue z` on `|z_j| ≤ 1/16` (replacing the corpus's `smallConvLower mValue = 2^{-150}`) | `BoseFixB1B/conv3SmallLowerFlat.lean` |
| `fibreBoundConvFlat` | the sharp fibre bound with the constant `16π·chiSupAbs·chiSmallNormFactor mValue/c` (feeding the previous piece into `wSmall1Pair_fibre_le_chiM_sharp`) | `BoseFixB1B/fibreBoundConvFlat.lean` |

**IMPORTANT — the *unconditional* flat branch (and hence `Work.BoseFixB1.PerBoxF` itself) is
REFUTED.**  Three delegated provers (`flatPairCount`, `flatBranchAlt`, `flatBranch`) independently
produced the same Jastrow/correlation-hole counterexample family; the ledger is
`Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md` (which supersedes
`FINDING_eps0_freedom.md`: the `ε₀`-freedom rescue fails quantitatively).  **The assigned target
survives**, because it carries `IsLowB`: the refuting family has kinetic energy
`≍ μ²ℓ³(4πR/d³)` against the `IsLowB` budget `≍ μ²ℓ³·4π(a v)`, so it needs `R/d³ ≲ a v`, false for
small diluteness.  The correct residual is therefore the **`IsLowB`-restricted** flat branch,
delegated as `Work.BoseFixB1B.flatBranchLowB` (`Submission/Work/BoseFixB1B/flatBranchLowB.lean`),
and the assembly below is threaded with `IsLowB`/`0 < normB` accordingly.

**REFUTED — do not re-state.**  `BoseFixB1B/flatPairCount` (the FINDING's §6.2 (PAIR):
`pairTermB ≥ c·(S_χ)²/(N·a·χ̂) − C(μ²aΓχ̂ + μa)N` on the flat branch, `S_χ = Σᵢ∫Φ²χ(x_i)`) was
**declared FALSE** by its prover: the flat hypothesis does *not* bound the particle number `n`, and
the "pair-dead" states `Φ = Πβ(x_i)·Π_{k<l}(1−η(x_k−x_l))` (with `η ≡ 1` on `ball 0 R ⊇ supp v` and
`κ = n/V` fixed) satisfy it with `pairTermB = 0` *exactly* (the state vanishes wherever
`v(x_k − x_l) ≠ 0`), while the proposed right-hand side is `Θ(V·N)` with a positive
`μ`-independent coefficient against an error slot that is `o(VN)`.  The **correct** reading of that
regime is that the pair-dead states are paid by the `ε_T`-*gap* slot instead (`sbKin ≥ gap·n₊` with
`n₊ ≈ N·n·κR³` for such states, and `gap/(μa v) = ½K_B²(a/v)(1+π^{-2})^{-1} → ∞`), while the
*quadratic* pair term is needed only in the complementary, `κ ≳ μ` regime; a statement that
combines these two mechanisms is not a "piece" but the flat branch itself, which is why the flat
branch stays a single delegated atom.  (The *linear* form of the same accounting — the FINDING's
(★′) — is also insufficient: it loses the exact `F` at the borderline `t ≈ μ`, where the
`w₂ ≥ w₁` slack `β = ĝω(0)/(8πa)` can be smaller than the loss.)

**The flat branch itself is NOT refuted by the hole family.**  See
`Submission/Work/BoseFixB1B/FINDING_eps0_freedom.md`: `γ₀` is chosen *before* `ε₀`, admissibility
only requires `μ(a v)³ ≤ ε₀`, and the gap coefficient `t^{-13/1292}/(2(1+π^{-2}))` is *unbounded*
as `ε₀ → 0`; with `ε₀ ≪ (γ₀/C)^{100}` the gap pays the hole states for every state of the flat
class, uniformly in `μ ≤ ε₀`.  (Two delegated provers split on this — `flatPairCount` and
`flatBranchAlt` returned FALSE on the strength of that family; the `ε₀`-freedom is why the
flat-branch *statement* survives them.)

## What this file also contains (proved here, sorry-free)

* §1 the sup/count chain of the sliding cutoff (`abs_chiSmall_le_decay`, `abs_chiSmallB_le_const`,
  `chiSmallB_sq_le_const_mul_self`, `nCountB_le_const_mul_sum`,
  `chiSmallB_le_const_mul_indicator`, `nCountB_le_const_mul_boxCount`) — the pointwise half of the
  smooth-count passage;
* §2 `perBoxErrCoeff_nonneg`, `perBoxF_to_smooth` (the wrapper) and `perBoxF_mono`
  (monotonicity of `PerBoxF` in `c₁` downwards and in `C` upwards);
* §3 `perBoxF_of_branches` (the branch assembly) and `perBoxSmoothHolds_of_goodSet`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The sup/count chain of the sliding cutoff -/

/-- `|χ_M z| ≤ chiSmallDecay M` (the `M`-dependent sup of the cosine bump). -/
lemma abs_chiSmall_le_decay {M : ℕ} (hM : 1 ≤ M) (z : EuclideanSpace ℝ (Fin 3)) :
    |chiSmall M z| ≤ chiSmallDecay M := by
  have h := chiSmall_decay_coord hM z 0
  have hle : max (1 / 2 - |z.ofLp (0 : Fin 3)|) 0 ≤ 1 :=
    max_le (by have := abs_nonneg (z.ofLp (0 : Fin 3)); linarith) (by norm_num)
  have hpow : (max (1 / 2 - |z.ofLp (0 : Fin 3)|) 0) ^ M ≤ 1 :=
    pow_le_one₀ (le_max_right _ _) hle
  calc |chiSmall M z| ≤ chiSmallDecay M * (max (1 / 2 - |z.ofLp (0 : Fin 3)|) 0) ^ M := h
    _ ≤ chiSmallDecay M * 1 :=
        mul_le_mul_of_nonneg_left hpow (chiSmallDecay_nonneg M)
    _ = chiSmallDecay M := by ring

/-- **The universal sup bound of the product cutoff**:
`|chiSmallB M ℓ d u x| ≤ K`, `K := chiSupAbs·chiSmallDecay M`. -/
lemma abs_chiSmallB_le_const {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u x : EuclideanSpace ℝ (Fin 3)) :
    |chiSmallB M ℓ d u x| ≤ chiSupAbs * chiSmallDecay M := by
  calc |chiSmallB M ℓ d u x|
      ≤ chiSupAbs * chiSmall M ((ℓ * d)⁻¹ • x - u) :=
        Work.SmallBoxSliding.abs_chiSmallB_le hM u x
    _ ≤ chiSupAbs * chiSmallDecay M :=
        mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans
            (abs_chiSmall_le_decay (M := M) hM ((ℓ * d)⁻¹ • x - u))) chiSupAbs_nonneg

/-- `χ² ≤ K·χ` for the product cutoff (`χ ≥ 0`). -/
lemma chiSmallB_sq_le_const_mul_self {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    (chiSmallB M ℓ d u x) ^ 2
      ≤ (chiSupAbs * chiSmallDecay M) * chiSmallB M ℓ d u x := by
  have h0 : 0 ≤ chiSmallB M ℓ d u x := Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hb : chiSmallB M ℓ d u x ≤ chiSupAbs * chiSmallDecay M := by
    calc chiSmallB M ℓ d u x ≤ |chiSmallB M ℓ d u x| := le_abs_self _
      _ ≤ chiSupAbs * chiSmallDecay M := abs_chiSmallB_le_const hM ℓ d u x
  nlinarith [h0, hb]

/-- **The smooth count is bounded by the `χ_{B(u)}`-sum** with the universal constant
`K = chiSupAbs·chiSmallDecay M`. -/
lemma nCountB_le_const_mul_sum {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.nCountB M ℓ d u x
      ≤ (chiSupAbs * chiSmallDecay M) * ∑ i : Fin n, chiSmallB M ℓ d u (x i) := by
  rw [Work.BoseFixB1.nCountB, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => chiSmallB_sq_le_const_mul_self hM ℓ d u (x i)

/-- **The support containment**: `χ_{B(u)}(x) ≤ K·1_{B(u)}(x)`, i.e. the cutoff is bounded by the
box indicator times its sup (`chiSmallB_support_big_box` + `chiSmallB_support_small_box_dist`). -/
lemma chiSmallB_le_const_mul_indicator {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    chiSmallB M ℓ d u x
      ≤ (chiSupAbs * chiSmallDecay M) * (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ dlBox ℓ d u
  · rw [Set.indicator_of_mem hx, mul_one]
    exact (le_abs_self _).trans (abs_chiSmallB_le_const hM ℓ d u x)
  · rw [Set.indicator_of_notMem hx, mul_zero]
    by_contra hcon
    have hpos : 0 < chiSmallB M ℓ d u x := lt_of_not_ge hcon
    refine hx ?_
    rw [mem_dlBox_iff]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · have h := abs_le.mp (chiSmallB_support_big_box hM hℓ (ne_of_gt hpos) j)
      rw [Set.mem_Icc]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · have h := abs_le.mp (chiSmallB_support_small_box_dist hM hℓ hd (ne_of_gt hpos) j)
      rw [Set.mem_Icc]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- **The smooth count is bounded by the box count**: `nCountB(x) ≤ K²·Σᵢ1_{B(u)}(xᵢ)`. -/
lemma nCountB_le_const_mul_boxCount {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixB1.nCountB M ℓ d u x
      ≤ (chiSupAbs * chiSmallDecay M) ^ 2
          * ∑ i : Fin n, (dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
  refine (nCountB_le_const_mul_sum hM ℓ d u x).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have hK : 0 ≤ chiSupAbs * chiSmallDecay M := mul_nonneg chiSupAbs_nonneg (chiSmallDecay_nonneg M)
  have h := chiSmallB_le_const_mul_indicator hM hℓ hd u (x i)
  have hnonneg : 0 ≤ (chiSupAbs * chiSmallDecay M) * (dlBox ℓ d u).indicator
      (fun _ => (1 : ℝ)) (x i) := by
    by_cases hmem : x i ∈ dlBox ℓ d u
    · rw [Set.indicator_of_mem hmem, mul_one]; exact hK
    · rw [Set.indicator_of_notMem hmem, mul_zero]
  nlinarith [h, hK, hnonneg]

/-! ## 2. `PerBoxF ⟹ PerBoxSmooth`, the error bracket, and the monotonicity of `PerBoxF` -/

/-- Elementary nonnegativity of the sliding cutoff's mass. -/
lemma chiMass_nonneg_cutB (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.SmallBoxSliding.chiMass M ℓ d u := by
  rw [Work.SmallBoxSliding.chiMass]
  exact integral_nonneg fun x => sq_nonneg _

/-- Elementary nonnegativity of the smooth count. -/
lemma nCountB_nonneg_cutB {M : ℕ} {ℓ d : ℝ} {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin 3)) : 0 ≤ Work.BoseFixB1.nCountB M ℓ d u x := by
  rw [Work.BoseFixB1.nCountB]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- **Nonnegativity of `PerBoxF`'s error bracket** (the `C`-coefficient):
`μ²(a v)Γ·χ·‖Φ‖² + μ(a v)‖Φ‖² ≥ 0`. -/
theorem perBoxErrCoeff_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    {u : EuclideanSpace ℝ (Fin 3)} :
    0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
          * ((R / (sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
              + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
          * chiMass (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d u
          * normB v μ n Φ
        + μ * (_root_.BoseGases.a v) * normB v μ n Φ := by
  have hKB : 0 ≤ (paramsAt μ (_root_.BoseGases.a v)).KB := by
    have ht : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
    have h : (paramsAt μ (_root_.BoseGases.a v)).KB = Work.BoseBox.fsXp (μ * (_root_.BoseGases.a v) ^ 3) (-6) := rfl
    rw [h]; exact le_of_lt (Work.BoseBox.fsXp_pos ht)
  have hΓ : 0 ≤ (R / (sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
      + (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (pow_nonneg hKB 3)
      (Real.rpow_nonneg (mul_nonneg (le_of_lt hμ) (pow_nonneg (le_of_lt hav) 3)) _))
  have hχ : 0 ≤ chiMass (paramsAt μ (_root_.BoseGases.a v)).M (sideAt μ (_root_.BoseGases.a v))
      (paramsAt μ (_root_.BoseGases.a v)).d u := chiMass_nonneg_cutB _ _ _ _
  have hN : 0 ≤ normB v μ n Φ := Work.BoseFixB1.normB_nonneg _
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (le_of_lt hav)) hΓ) hχ) hN)
    (mul_nonneg (mul_nonneg (le_of_lt hμ) (le_of_lt hav)) hN)

/-- **The wrapper**: `PerBoxF` implies `PerBoxSmooth`'s conclusion at the *same* constants.
(The two displays differ only by the rearrangement of the `C`-bracket:
`fWeight = W·∫Φ²F(t)` and `boxErrShape = μ²(a v)Γχ + μ(a v)`.) -/
theorem perBoxF_to_smooth {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hbox : Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    c₁ * fWeight v h μ (Φ : Submission.BoseGases.X n → ℝ) u
      ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
        + (1 / 2) * μ ^ 2 * (Work.BoseFixB1.w1MassB h
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        + C * boxErrShape v h R μ u
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
  simp only [Work.BoseFixB1.PerBoxF, fWeight, boxErrShape] at hbox ⊢
  linarith [hbox]

/-- **`PerBoxF` is monotone**: lowering the coefficient `c₁` and raising the error constant `C`
only weakens the inequality. -/
theorem perBoxF_mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R c₁ C c₁' C' μ : ℝ} {n : ℕ}
    {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hμ : 0 < μ) (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hav : 0 < _root_.BoseGases.a v)
    (hc₁ : c₁ ≤ c₁') (hC : C' ≤ C) (hbox : Work.BoseFixB1.PerBoxF v h R c₁' C' μ n Φ u) :
    Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  have hW : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.BoseFixB1.w1MassB_nonneg h hv hvrad hR hv_supp hℓ hd u
  have hF : 0 ≤ ∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
      (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
          Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (psiWeight_nonneg hμ (div_nonneg (nCountB_nonneg_cutB x) (chiMass_nonneg_cutB _ _ _ _)))
  have hP : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      * (∫ x in Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
          (Φ x) ^ 2 * Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
              Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)) := mul_nonneg hW hF
  have hE : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
          + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      + μ * (_root_.BoseGases.a v)
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have h := perBoxErrCoeff_nonneg (v := v) (R := R) (μ := μ) (n := n) (u := u) hμ hav
      (Φ : Submission.BoseGases.X n → ℝ)
    simpa using h
  simp only [Work.BoseFixB1.PerBoxF] at hbox ⊢
  nlinarith [hbox, mul_le_mul_of_nonneg_right hc₁ hP, mul_le_mul_of_nonneg_right hC hE]

/-! ## 3. The branch assembly, and `PerBoxSmooth` from the `goodSet` conclusion -/

/-- **The `goodSet` conclusion from the flat branch, the (strengthened) gap branch and the
(proved) thin case.**

The flat branch is consumed at *its own* threshold `γ₀`; the gap branch is consumed at the *same*
`γ₀` — this is why the gap branch is taken here in the strengthened form "at every prescribed
threshold" (`Work.BoseFixB1B.gapAtAll`, the re-run of the proved
`Work.BoseFixB1.perBoxF_of_gapPayment` with the constant `c'` chosen from the threshold): the
proved `perBoxF_of_gapPayment` only produces *some* `γ_gap`, and the two branches must meet at a
common threshold (`γ₀ ≥ γ_gap`), so the flat branch's own threshold must be usable for the gap
side as well. -/
theorem perBoxF_of_branches {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    (hflat : ∃ γ₀ ε₀ C : ℝ, 0 < γ₀ ∧ 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → 0 < μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          ¬ Work.BoseFixB1.IsThinBox v h μ u →
          Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
              (Φ : Submission.BoseGases.X n → ℝ)
            < γ₀ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.PerBoxF v h R (1 / 4) C μ n Φ u)
    (hgap : ∀ γ : ℝ, 0 < γ → ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          γ * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseFixB1.PerBoxF v h R (1 / 4) C μ n Φ u) :
    ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → 0 < μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u := by
  obtain ⟨γf, εf, Cf, hγf, hεf, hCf, hF⟩ := hflat
  obtain ⟨εg, Cg, hεg, hCg, hG⟩ := hgap γf hγf
  obtain ⟨εt, c₁t, Ct, hεt, hc₁t, hCt, hT⟩ :=
    Work.BoseFixB1.perBoxF_thin_holds (v := v) (h := h) (R := R) hv hvrad hR hv_supp
  refine ⟨min εt (min εf εg), min c₁t (1 / 4), max Ct (max Cf Cg),
    lt_min hεt (lt_min hεf hεg), lt_min hc₁t (by norm_num),
    le_trans hCt (le_max_left Ct (max Cf Cg)), ?_⟩
  intro μ hAdm hμpos n Φ hnorm hlow u hu
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hava : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hAdmt : Work.BoseBoxFix.Adm v εt μ :=
    Work.BoseFixB1.Adm.mono (ε₀' := min εt (min εf εg)) hAdm (min_le_left _ _)
  have hAdmf : Work.BoseBoxFix.Adm v εf μ :=
    Work.BoseFixB1.Adm.mono (ε₀' := min εt (min εf εg)) hAdm
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono (ε₀' := min εt (min εf εg)) hAdm
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hc₁t' : min c₁t (1 / 4) ≤ c₁t := min_le_left _ _
  have hc₁q : min c₁t (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hCt' : Ct ≤ max Ct (max Cf Cg) := le_max_left _ _
  have hCf' : Cf ≤ max Ct (max Cf Cg) := le_trans (le_max_left Cf Cg) (le_max_right _ _)
  have hCg' : Cg ≤ max Ct (max Cf Cg) := le_trans (le_max_right Cf Cg) (le_max_right _ _)
  by_cases hthin : Work.BoseFixB1.IsThinBox v h μ u
  · exact perBoxF_mono hv hvrad hR hv_supp hμ hℓ hd hava hc₁t' hCt'
      (hT μ hAdmt n Φ u hu hthin)
  · by_cases hcase : γf * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
    · exact perBoxF_mono hv hvrad hR hv_supp hμ hℓ hd hava hc₁q hCg'
        (hG μ hAdmg n Φ u hcase)
    · exact perBoxF_mono hv hvrad hR hv_supp hμ hℓ hd hava hc₁q hCf'
        (hF μ hAdmf hμpos n Φ hnorm hlow u hu hthin (lt_of_not_ge hcase))

/-- **`PerBoxSmooth` from the `IsLowB`-restricted `goodSet` conclusion** (the wrapper of §2 plus
the containment `interiorSet ⊆ goodSet`).  The `IsLowB`/`0 < normB` data are exactly what
`PerBoxSmooth`'s body carries, so the restriction is free here — and it is *necessary*: the
unrestricted per-box crux `PerBoxF` is FALSE (see
`Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`). -/
theorem perBoxSmoothHolds_of_goodSet {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R J : ℝ}
    (hall : ∃ ε₀ c₁ C : ℝ, 0 < ε₀ ∧ 0 < c₁ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → 0 < μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          Work.BoseFixB1.PerBoxF v h R c₁ C μ n Φ u) :
    Work.BoseFixB1B.PerBoxSmooth v h R J := by
  obtain ⟨ε₀, c₁, C, hε₀, hc₁, hC, H⟩ := hall
  refine ⟨ε₀, c₁, C, hε₀, hc₁, hC, ?_⟩
  intro μ hAdm hμpos n Φ hnorm hlow u hu
  exact perBoxF_to_smooth (H μ hAdm hμpos n Φ hnorm hlow u
    (Work.SmallBoxSliding.interiorSet_subset_goodSet (Work.BoseFixB1.adm_mu_pos hAdm) hu))

/-! ## 3bis. The frozen target **from the chapter's single atom** `FlatBranchMaxFree`

`Work.BoseFixB1B.FlatBranchMaxFree v h R` (`Submission/Work/BoseFixB1B/flatBranchMaxFreeDefs.lean`)
is FS `thm:smallbox`'s *flat arm* at the sliding box — the *one* analytic atom on which the whole
per-box / count-window chapter now converges (`countWindowUnifConsumers.lean`,
`nodeB1B_of_aprioriUnif.lean`, `LowCountWindowAllJ.lean`, `flatBranchMaxFree_of_branches.lean` all
consume it; the sector-core route of §4 is dead at the statement level because the low core's
`(R5)` is a Bogoliubov port at the *frozen* (ball) slot window, and every such port is FALSE — see
`FINDING_PerBoxSmoothHolds_session2.md` §1).

`perBoxSmooth_of_flatBranchMaxFree` below proves the frozen target **from that single atom**,
using only PROVED corpus results:

* the three-arm split of FS `thm:smallbox` (`perBoxF_of_branches` of §3): thin
  (`Work.BoseFixB1.perBoxF_thin_holds`), gap (`Work.BoseFixB1B.gapAtAll`, at *every* prescribed
  threshold) and flat (the atom);
* the **`J`-bookkeeping**: the atom's flat arm is stated on the `LowMax` class, while the frozen
  target quantifies a general `J ≥ lhyC` with only the diluteness threshold `ε₀` at our disposal.
  Shrinking `ε₀ ≤ J^{-323/18}` turns `Adm` into `J ≤ K_B³(μ)` (`Work.BoseBox.KB_cube_ge`), whence
  `IsLowB v h J μ n Φ → LowMax v h μ n Φ` (`Work.BoseFixB1B.LowMax_of_isLowB`).  This is exactly
  the bookkeeping the session-1 reduction of this file used for the sector cores, and it is
  *not* cosmetic: it is also what puts the node inside FS's *deep* window
  `t = μ(a v)³ ≤ J^{-323/18}`, in which the corner/shell-potential family of
  `Work.BoseFixR.not_low_particle_bound_of_corner` (the corner `v ≡ 0` on `ball(0,2ℓ)`, which
  requires `2ℓ ≤ R`) is incompatible with `Adm`'s regime `R ≤ ℓ·chiR0`
  (`Work.BoseFixB1.regime_sideAt_ge`) — see `FINDING_perBoxFLowSupply_session1.md` §2.

**Note on the coefficient `c₁`.**  `FlatBranchMaxFree` is stated at a *free* `c₁f > 0` while the
thick/gap/thin arms deliver `c₁ = 1/4`; since `PerBoxF` is *antitone* in `c₁` (`perBoxF_mono`,
§2), the three arms meet at the common coefficient `min c₁f (1/4) > 0`.  This is why the assembly
below is written out here rather than consumed from `flatBranchMaxFree_of_branches` — that module
is *downstream* of this one (it imports it for `perBoxF_mono`), so it cannot be imported here. -/

/-- **The frozen target from the chapter's single atom.**  `FlatBranchMaxFree v h R` (the flat arm
of FS `thm:smallbox` at the sliding box, `LowMax`-restricted) together with the PROVED thin and
gap arms gives `PerBoxSmooth v h R J` at the frozen `J ≥ lhyC`. -/
theorem perBoxSmooth_of_flatBranchMaxFree {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {R J : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hJ : Work.UBB.lhyC ≤ J)
    (hfree : Work.BoseFixB1B.FlatBranchMaxFree v h R) :
    Work.BoseFixB1B.PerBoxSmooth v h R J := by
  obtain ⟨γf, εf, c₁f, Cf, hγf, hεf, hc₁f, hCf, hF⟩ := hfree
  obtain ⟨εg, Cg, hεg, hCg, hG⟩ :=
    Work.BoseFixB1B.gapAtAll v h hv hv1 hvrad hR hv_supp hav γf hγf
  obtain ⟨εt, c₁t, Ct, hεt, hc₁t, hCt, hT⟩ :=
    Work.BoseFixB1.perBoxF_thin_holds (v := v) (h := h) (R := R) hv hvrad hR hv_supp
  have hJpos : 0 < J := lt_of_lt_of_le Work.UBB.lhyC_pos hJ
  refine perBoxSmoothHolds_of_goodSet (v := v) (h := h) (R := R) (J := J) ?_
  refine ⟨min (J ^ (-(323 / 18 : ℝ))) (min εf (min εg εt)), min (min c₁f c₁t) (1 / 4),
    max (max Cf (max Cg Ct)) 0,
    lt_min (Real.rpow_pos_of_pos hJpos _) (lt_min hεf (lt_min hεg hεt)),
    lt_min (lt_min hc₁f hc₁t) (by norm_num), le_max_right _ _, ?_⟩
  intro μ hAdm hμpos n Φ hnorm hlow u hu
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hava : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hAdm
  have hAdmF : Work.BoseBoxFix.Adm v εf μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmg : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hAdmt : Work.BoseBoxFix.Adm v εt μ :=
    Work.BoseFixB1.Adm.mono hAdm
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  -- ## the `J`-bookkeeping: `Adm` at `ε₀ ≤ J^{-323/18}` gives `J ≤ K_B³`, hence `LowMax`
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ J ^ (-(323 / 18 : ℝ)) :=
    le_trans hAdm.2.1 (min_le_left _ _)
  have hJle : J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 :=
    Work.BoseBox.KB_cube_ge hμpos hava hJpos hdil
  have hLow : Work.BoseFixB1B.LowMax v h μ n Φ :=
    Work.BoseFixB1B.LowMax_of_isLowB hava (le_of_lt hℓ) hJle hlow
  -- ## the three arms at the common coefficient `c₁ = min (min c₁f c₁t) (1/4)`
  have hc₁f' : min (min c₁f c₁t) (1 / 4) ≤ c₁f :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hc₁t' : min (min c₁f c₁t) (1 / 4) ≤ c₁t :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hc₁q : min (min c₁f c₁t) (1 / 4) ≤ 1 / 4 := min_le_right _ _
  have hCf' : Cf ≤ max (max Cf (max Cg Ct)) 0 :=
    le_trans (le_max_left Cf (max Cg Ct)) (le_max_left (max Cf (max Cg Ct)) 0)
  have hCg' : Cg ≤ max (max Cf (max Cg Ct)) 0 :=
    le_trans (le_max_left Cg Ct)
      (le_trans (le_max_right Cf (max Cg Ct)) (le_max_left (max Cf (max Cg Ct)) 0))
  have hCt' : Ct ≤ max (max Cf (max Cg Ct)) 0 :=
    le_trans (le_max_right Cg Ct)
      (le_trans (le_max_right Cf (max Cg Ct)) (le_max_left (max Cf (max Cg Ct)) 0))
  by_cases hthin : Work.BoseFixB1.IsThinBox v h μ u
  · exact perBoxF_mono hv hvrad hR hv_supp hμpos hℓ hd hava hc₁t' hCt'
      (hT μ hAdmt n Φ u hu hthin)
  · by_cases hcase : γf * (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            (Φ : Submission.BoseGases.X n → ℝ)
    · exact perBoxF_mono hv hvrad hR hv_supp hμpos hℓ hd hava hc₁q hCg'
        (hG μ hAdmg n Φ u hcase)
    · exact perBoxF_mono hv hvrad hR hv_supp hμpos hℓ hd hava hc₁f' hCf'
        (hF μ hAdmF hμpos n Φ hnorm hLow u hu hthin (lt_of_not_ge hcase))

/-- **Piece 1 of the chapter** (inhabiting `Work.BoseFixB1B.PerBoxSmooth`): FS `thm:smallbox`
(`final_v2.tex` l. 3907) at the sliding box `B(u)`, in the state-level *smooth-count* form of the
frozen vocabulary, with free constants.  The statement is *strictly stronger* than
`Work.BoseFixB1B.perBoxIntegratedPos` (the latter is its `I₋`-integral: see
`Work.BoseFixB1B.perBoxIntegratedPos_of_perBoxSmooth` in the sibling file
`Submission/Work/BoseFixB1B/perBoxIntegratedPos.lean`, which needs in addition the
`u`-bookkeeping — the proven mass normalisation `Work.SmallBoxSliding.integral_chiMass_eq`, the
finiteness of `I₋`, the FS parameter regime `(R/(dℓ))² ≤ K_B³(μ(a v)³)^{1/2}` and the
integrability of the three integrands).

**The proof**: the reduction `perBoxSmooth_of_flatBranchMaxFree` above, applied to the chapter's
single atom `Work.BoseFixB1B.FlatBranchMaxFree v h R` (the flat arm of FS `thm:smallbox` at the
sliding box, in its weakest known form — free threshold, free coefficient, `LowMax`-restricted),
which is held by `Submission/Work/BoseFixB1B/flatBranchMaxFree_holds.lean`.  Every other input
(thin arm, gap arm at every threshold, the `J`-bookkeeping, the wrapper
`perBoxF_to_smooth`) is PROVED and axiom-clean in this module or in its (cycle-free) imports. -/
theorem PerBoxSmoothHolds (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    Work.BoseFixB1B.PerBoxSmooth v h R J :=
  perBoxSmooth_of_flatBranchMaxFree (v := v) (h := h) (R := R) (J := J)
    hv hv1 hvrad hR hv_supp hav hJ
    (by
      -- the chapter's single atom: FS `thm:smallbox`'s flat arm at the sliding box
      sorry)


/-! ## 4. The reduction of the frozen target to the two low-restricted **sector cores**

**This is the assembly of the frozen target.**  `Submission/Work/BoseFixB1B/sectorFrontier.lean`
(and every other file of the node's chain) *imports this module*, so its atoms cannot be imported
here; this section therefore re-runs, inside this module, the two steps it performs:

* `SectorCoreLowAtL` / `SectorCoreHighAtL` below are *character-for-character*
  `Work.BoseFixB1B.PerSectorSmoothLowDensAtL` / `Work.BoseFixB1B.PerSectorSmoothHighDensAtL`
  of `sectorFrontier.lean` (renamed only because the same names cannot live in two modules of one
  cone);
* `perBoxSmoothHolds_of_sectorCores` proves `Work.BoseFixB1B.PerBoxSmooth v h R J` from them, in
  three steps:
  1. the two cores at a *common* constant triple (`min c₁ c₂`, `max C₁ C₂`), through the PROVED
     `Work.BoseFixB1.SectorSmoothIneq_mono`;
  2. the **sector summation** `perBoxF_of_sectorIneqLow` (copied verbatim from the private lemma of
     `sectorFrontier.lean`, itself a copy of `perBoxFWeight_of_perSectorSmooth`'s body): summing
     the sector inequalities and using the PROVED `Work.BoseFixB1.sectorFPpartition`,
     `Work.BoseFixB1B.sectorMass_sum` and `Work.BoseFixB1.sbWordSectorAdditiveAdm` gives the
     good-set per-box bound `PerBoxF`;
  3. the wrapper `perBoxSmoothHolds_of_goodSet` of §3, together with the removal of the
     `J ≤ K_B³` hypothesis of the sector frontier: `Adm v (min ε₀ (J^{−323/18})) μ` gives
     `μ (a v)³ ≤ J^{−323/18}`, whence `J ≤ K_B³` by `Work.BoseBox.KB_cube_ge`.

**The `J`-bookkeeping is not cosmetic.**  The frozen target quantifies `J` with only the lower
bound `lhyC ≤ J`, while FS's own a priori hypothesis `eq:aprioriPsi` carries `0 < J ≤ K_B³`, and
the corpus's per-box providers all carry `J ≤ K_B³` *as a hypothesis on `μ`*.  The two are
reconciled by the freedom in the target's own `∃ ε₀`: taking `ε₀ ≤ J^{−323/18}` makes `J ≤ K_B³`
a *consequence* of `Adm` (`Work.BoseBox.KB_cube_ge`).  This is also where the correlation-hole
(Jastrow) states are kept out of the class: their kinetic energy exceeds FS's threshold
`4πμ²(a v)ℓ³(1 − J√(μ(a v)³))` unless `ε₀ ≳ J^{−1}`, cf.
`Submission/Work/BoseFixB1B/FINDING_perBoxF_refuted_lowB_survives.md`.

**So the frozen target is reducible to exactly the two atoms that the fleet's own node
`lowCountBound` consumes** (`sectorFrontier.lean`'s `lowCountBound_of_sectorCores`); the only
difference is the `IsLowB` window, which these cores carry.
-/

section

set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The low-density core, low-state-restricted** — verbatim
`Work.BoseFixB1B.PerSectorSmoothLowDensAtL` of `Submission/Work/BoseFixB1B/sectorFrontier.lean`
(same `Prop`, renamed because that module imports this one). -/
def SectorCoreLowAtL (v : E3 → ℝ) (h : ScatSol v) (R J : ℝ) (ε₀ c C : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1.bSide v μ)),
      0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          Work.BoseFixB1.sectorDensLow v μ Φ u k →
            Work.BoseFixB1.SectorSmoothIneq v h R c C μ Φ u k

/-- **The high-density core, low-state-restricted** — verbatim
`Work.BoseFixB1B.PerSectorSmoothHighDensAtL` of `Submission/Work/BoseFixB1B/sectorFrontier.lean`
(same `Prop`, renamed because that module imports this one). -/
def SectorCoreHighAtL (v : E3 → ℝ) (h : ScatSol v) (R J : ℝ) (ε₀ c C : ℝ) : Prop :=
  ∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1.bSide v μ)),
      0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
      ∀ u : E3, u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
        ∀ k ∈ Finset.range (n + 1),
          ¬ Work.BoseFixB1.sectorDensLow v μ Φ u k →
            Work.BoseFixB1.SectorSmoothIneq v h R c C μ Φ u k

private lemma perBoxF_of_sectorIneqLow {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {ε₀ ε₀w c C J : ℝ}
    (hmain : ∀ μ : ℝ, Adm v ε₀ μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1.bSide v μ)),
        0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
        ∀ u : E3, u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          ∀ k ∈ Finset.range (n + 1),
            Work.BoseFixB1.SectorSmoothIneq v h R c C μ Φ u k)
    (hadd : ∀ μ : ℝ, Adm v ε₀w μ → ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v)))
      (u : E3), Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)
        = ∑ k ∈ Finset.range (n + 1),
            (Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.bM v μ) u
                (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ))
              + Work.BoseFixB1.sbPot h μ u (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ)))) :
    ∀ μ : ℝ, Adm v (min ε₀ ε₀w) μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))),
        0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
        ∀ u : E3, u ∈ goodSet (sideAt μ (a v)) (paramsAt μ (a v)).d μ →
          Work.BoseFixB1.PerBoxF v h R c C μ n Φ u := by
  intro μ hAdm hJK n Φ hnorm hlow u hu
  have hAdms : Adm v ε₀ μ := Work.BoseFixB1.Adm.mono (ε₀' := min ε₀ ε₀w) (ε₀ := ε₀) hAdm (min_le_left _ _)
  have hAdmw : Adm v ε₀w μ := Work.BoseFixB1.Adm.mono (ε₀' := min ε₀ ε₀w) (ε₀ := ε₀w) hAdm (min_le_right _ _)
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ Work.BoseFixB1.bM v μ := by
    change 1 ≤ Work.BoseBox.mValue
    decide
  -- ## the per-sector inequalities, summed
  have hterm : (∑ k ∈ Finset.range (n + 1),
        (c * (Work.BoseFixB1.bW v h μ u * (∫ x in abox n (Work.BoseFixB1.bSide v μ),
            (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
              psiWeight 1 μ (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u x
                / chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u)))
          - (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
              * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Φ : X n → ℝ) k
          - C * Work.BoseFixB1.bErr v R μ u
              * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Φ : X n → ℝ) k))
      ≤ ∑ k ∈ Finset.range (n + 1),
          (Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.bM v μ) u
              (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ))
            + Work.BoseFixB1.sbPot h μ u (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ))) :=
    Finset.sum_le_sum fun k hk => hmain μ hAdms hJK n Φ hnorm hlow u hu k hk
  -- ## the four rewrites
  have hFint := Work.BoseFixB1.sectorFPpartition (v := v) (μ := μ) hAdm.1 n Φ u
  have hmass : (∑ k ∈ Finset.range (n + 1),
        Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) (Φ : X n → ℝ) k)
      = Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    simpa only [Work.BoseFixB1.bSide, Work.BoseFixB1.bA, Work.BoseFixB1.bD,
      Work.BoseFixB1B.PBB, Work.BoseFixB1B.PBℓ,
      Work.BoseFixB1B.PBd] using Work.BoseFixB1B.sectorMass_sum (v := v) (μ := μ) Φ u
  have hword : Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ)
      = ∑ k ∈ Finset.range (n + 1),
          (Work.BoseFixB1.sbKin (v := v) μ (Work.BoseFixB1.bM v μ) u
              (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ))
            + Work.BoseFixB1.sbPot h μ u (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ))) := by
    simpa only [Work.BoseFixB1.sbKin, Work.BoseFixB1.sbPot, Work.BoseFixB1.bA, Work.BoseFixB1.bD, Work.BoseFixB1.bM,
      Work.BoseFixB1.bSide, Work.BoseFixB1B.PBB, Work.BoseFixB1B.PBℓ,
      Work.BoseFixB1B.PBd, Work.BoseFixB1B.PBM, Work.BoseFixB1B.PBeT]
      using hadd μ hAdmw n Φ u
  -- ## assemble: pull the constants out of the sums, then the three identities
  have hsub : (∑ k ∈ Finset.range (n + 1),
        (c * (Work.BoseFixB1.bW v h μ u * (∫ x in abox n (Work.BoseFixB1.bSide v μ),
            (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
              psiWeight 1 μ (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u x
                / chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u)))
          - (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
              * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Φ : X n → ℝ) k
          - C * Work.BoseFixB1.bErr v R μ u
              * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Φ : X n → ℝ) k))
      = (∑ k ∈ Finset.range (n + 1),
            c * (Work.BoseFixB1.bW v h μ u * (∫ x in abox n (Work.BoseFixB1.bSide v μ),
                (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
                  psiWeight 1 μ (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u x
                    / chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                        (Work.BoseFixB1.bD v μ) u))))
        - (∑ k ∈ Finset.range (n + 1), (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
              * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Φ : X n → ℝ) k)
        - (∑ k ∈ Finset.range (n + 1), C * Work.BoseFixB1.bErr v R μ u
              * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u)
                  (Φ : X n → ℝ) k) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hA : (∑ k ∈ Finset.range (n + 1),
          c * (Work.BoseFixB1.bW v h μ u * (∫ x in abox n (Work.BoseFixB1.bSide v μ),
              (Work.FockBridge.sectorPiece (Work.BoseFixB1.bA v μ u) k (Φ : X n → ℝ) x) ^ 2 *
                psiWeight 1 μ (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u x
                  / chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                      (Work.BoseFixB1.bD v μ) u))))
      = c * (Work.BoseFixB1.bW v h μ u * (∫ x in abox n (Work.BoseFixB1.bSide v μ),
            (Φ x) ^ 2 * psiWeight 1 μ
              (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                  (Work.BoseFixB1.bD v μ) u x
                / chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                    (Work.BoseFixB1.bD v μ) u))) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hFint]
  have hB : (∑ k ∈ Finset.range (n + 1), (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
          * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) (Φ : X n → ℝ) k)
      = (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
          * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    rw [← Finset.mul_sum, hmass]
  have hD : (∑ k ∈ Finset.range (n + 1), C * Work.BoseFixB1.bErr v R μ u
          * Work.FockBridge.sectorMass (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bA v μ u) (Φ : X n → ℝ) k)
      = C * Work.BoseFixB1.bErr v R μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ) := by
    rw [← Finset.mul_sum, hmass]
  rw [← hword] at hterm
  have hgoal : c * (Work.BoseFixB1.bW v h μ u * (∫ x in abox n (Work.BoseFixB1.bSide v μ),
        (Φ x) ^ 2 * psiWeight 1 μ
          (Work.BoseFixB1.nCountB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
              (Work.BoseFixB1.bD v μ) u x
            / chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
                (Work.BoseFixB1.bD v μ) u)))
      - (1 / 2) * μ ^ 2 * Work.BoseFixB1.bW v h μ u
          * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      - C * Work.BoseFixB1.bErr v R μ u * Work.BoseBoxFix.normB v μ n (Φ : X n → ℝ)
      ≤ Work.BoseFixB1.sbWord h μ u (Φ : X n → ℝ) := by
    rw [← hA, ← hB, ← hD, ← hsub]
    exact hterm
  unfold Work.BoseFixB1.PerBoxF
  simp only [Work.BoseFixB1.bW, Work.BoseFixB1.bErr, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
    Work.BoseFixB1.bM, Work.BoseFixB1.bA] at hgoal
  exact le_of_eq_of_le (by ring) hgoal


/-- **The frozen target from the two low-restricted sector cores** — the assembly described in the
section docstring.  Together with `sectorFrontier.lean`'s `lowCountBound_of_sectorCores` this shows
that the per-box node and the count node are *one* obligation, stated in two vocabularies. -/
theorem perBoxSmoothHolds_of_sectorCores {v : E3 → ℝ} {h : ScatSol v} {R J : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    (hJ : Work.UBB.lhyC ≤ J)
    (hL : ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 ≤ C ∧ SectorCoreLowAtL v h R J ε₀ c C)
    (hH : ∃ ε₀ c C : ℝ, 0 < ε₀ ∧ 0 < c ∧ 0 ≤ C ∧ SectorCoreHighAtL v h R J ε₀ c C) :
    Work.BoseFixB1B.PerBoxSmooth v h R J := by
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, hlow⟩ := hL
  obtain ⟨ε₂, c₂, C₂, hε₂, hc₂, hC₂, hhigh⟩ := hH
  -- ## 1. the two cores at a common constant triple
  have hmain : ∀ μ : ℝ, Adm v (min ε₁ ε₂) μ → J ≤ (paramsAt μ (a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseFixB1.bSide v μ)),
        0 < normB v μ n (Φ : X n → ℝ) → IsLowB v h J μ n Φ →
        ∀ u : E3, u ∈ goodSet (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) μ →
          ∀ k ∈ Finset.range (n + 1),
            Work.BoseFixB1.SectorSmoothIneq v h R (min c₁ c₂) (max C₁ C₂) μ Φ u k := by
    intro μ hAdm hJK n Φ hnorm hlow' u hu k hk
    have hAdm₁ : Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAdm₂ : Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
    by_cases hd : Work.BoseFixB1.sectorDensLow v μ Φ u k
    · exact Work.BoseFixB1.SectorSmoothIneq_mono hv hvrad hv_supp hR hAdm₁ (min_le_left _ _)
        (le_max_left _ _) Φ u k (hlow μ hAdm₁ hJK n Φ hnorm hlow' u hu k hk hd)
    · exact Work.BoseFixB1.SectorSmoothIneq_mono hv hvrad hv_supp hR hAdm₂ (min_le_right _ _)
        (le_max_right _ _) Φ u k (hhigh μ hAdm₂ hJK n Φ hnorm hlow' u hu k hk hd)
  -- ## 2. the sector summation
  obtain ⟨εw, hεw, hadd⟩ :=
    Work.BoseFixB1.sbWordSectorAdditiveAdm (v := v) h hv hv1 hvrad hR hv_supp hav
  have hεb : 0 < min (min ε₁ ε₂) εw := lt_min (lt_min hε₁ hε₂) hεw
  have hbody := perBoxF_of_sectorIneqLow h hv hv1 hvrad hR hv_supp hav hmain hadd
  -- ## 3. the wrapper of §3, with the diluteness threshold `ε₀ ≤ J^{-323/18}`
  have hJpos : 0 < J := lt_of_lt_of_le Work.UBB.lhyC_pos hJ
  refine perBoxSmoothHolds_of_goodSet (v := v) (h := h) (R := R) (J := J) ?_
  refine ⟨min (min (min ε₁ ε₂) εw) (J ^ (-(323 / 18 : ℝ))), min c₁ c₂, max C₁ C₂,
    lt_min hεb (Real.rpow_pos_of_pos hJpos _), lt_min hc₁ hc₂, le_max_of_le_left hC₁, ?_⟩
  intro μ hAdm hμpos n Φ hnorm hlow' u hu
  have hJle : J ≤ (paramsAt μ (a v)).KB ^ 3 :=
    Work.BoseBox.KB_cube_ge hAdm.1 hav hJpos (le_trans hAdm.2.1 (min_le_right _ _))
  exact hbody μ (Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)) hJle n Φ hnorm hlow' u hu


/-! ## 5. The low core from the pair/background ledger (`LOWN`)

In the low-density branch (`sectorDensLow`) the crude `F`-debit row (PROVED:
`Work.BoseFixB1.sectorPiece_debit_crude`, `∫Φ_k²F(t) ≤ 2μ²m_k`) is *absorbed exactly* by the
target's own background `−½μ²·bW·m_k` as soon as `c ≤ 1/4`; what is left is the **pair/background
ledger**

    (LOWN)   − C·bErr·m_k  ≤  sbKin(Φ_k) + sbPot(Φ_k) ,        m_k = ∫Φ_k² .

This is the *alternative* route to the low core: it never mentions the `A₀`-payment nor the pairing
`boxA2`, so it is **not** exposed to the two-window mismatch that blocks the payment route
(`SectorAux/FINDING_localisedAppBogSectorInd_FALSE.md`).  For a flat state at density `ρ ≤ μ` the
true balance is `μ·fibSum ≈ μ²M₁ρm_k` against `½·pairSum ≈ ½ρ²M₂m_k` plus the background, i.e. it is
the arithmetic inequality `M₁(λ−½) ≤ ½λ²M₂` (`λ = ρ/μ ∈ [0,1]`), which holds **iff** `M₂ ≥ M₁` (the
PROVED Born-gap `w1MassB_le_flatPairMassB1`): the maximum of `M₁(λ−½) − ½λ²M₂` on `[0,1]` is
`½M₁(M₁/M₂ − 1) ≤ 0`.  So `(LOWN)` is what the pair-Jensen/void rows must deliver. -/

/-- **The flat pair/background ledger at density `ρ = λμ ≤ μ`.**  `M₁(lam−½) ≤ ½lam²M₂` for
`0 ≤ lam ≤ 1` and `M₁ ≤ M₂`; this is the arithmetic content of `(LOWN)` at a flat state. -/
theorem lowDensBalance {M₁ M₂ lam : ℝ} (hM₁ : 0 ≤ M₁) (hM : M₁ ≤ M₂)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    M₁ * (lam - 1 / 2) ≤ (1 / 2) * lam ^ 2 * M₂ := by
  have hM2 : 0 ≤ M₂ := le_trans hM₁ hM
  rcases eq_or_lt_of_le hM2 with h0 | hpos
  · have hM10 : M₁ = 0 := le_antisymm (hM.trans (le_of_eq h0.symm)) hM₁
    rw [hM10, ← h0]
    norm_num
  · refine le_of_mul_le_mul_right ?_ hpos
    nlinarith [sq_nonneg (lam * M₂ - M₁), hM, hM₁, hlam0, hlam1]

/-- **The mean-field balance (the content of `(LOWN)`, with the background kept).**  For
`M₁ ≤ M₂`, `0 ≤ μ`, `0 ≤ ρ` and `c ≤ 1/2`,

    c·M₁·F(ρ) + μ·M₁·ρ − ½μ²M₁  ≤  ½·M₂·ρ² ,      F(ρ) = μ(ρ−μ)²/(ρ+μ) .

The proof is the *square*: `c·F(ρ) ≤ ½(ρ−μ)²` (for `c ≤ 1/2`) together with the identity
`½M₁(ρ−μ)² + μM₁ρ − ½μ²M₁ = ½M₁ρ²`; the Born gap `M₂ ≥ M₁` is what pays **at** `ρ = μ`, where the
square vanishes — that is the content of `lowDensBalance` (§5 above) and of FS's mean-field
ledger. -/
theorem meanFieldBalance {M₁ M₂ μ ρ c : ℝ} (hM₁ : 0 ≤ M₁) (hM : M₁ ≤ M₂) (hμ : 0 < μ)
    (hρ : 0 ≤ ρ) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) :
    c * M₁ * (μ * (ρ - μ) ^ 2 / (ρ + μ)) + μ * M₁ * ρ - (1 / 2) * μ ^ 2 * M₁
      ≤ (1 / 2) * M₂ * ρ ^ 2 := by
  have hden : 0 < ρ + μ := by linarith
  have hsq : 0 ≤ (ρ - μ) ^ 2 := sq_nonneg _
  have hF : μ * (ρ - μ) ^ 2 / (ρ + μ) ≤ (ρ - μ) ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [hsq, hμ, hρ]
  have h1 : c * (μ * (ρ - μ) ^ 2 / (ρ + μ)) ≤ (1 / 2) * (ρ - μ) ^ 2 := by
    nlinarith [hF, hc, hc0]
  have h2 : c * M₁ * (μ * (ρ - μ) ^ 2 / (ρ + μ)) ≤ (1 / 2) * M₁ * (ρ - μ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hM₁]
  have h3 : (1 / 2) * M₁ * (ρ - μ) ^ 2 + μ * M₁ * ρ - (1 / 2) * μ ^ 2 * M₁
      = (1 / 2) * M₁ * ρ ^ 2 := by ring
  nlinarith [h2, h3, hM₁, hM, hsq, mul_nonneg hM₁ hsq]

/-- **The same balance at the *flat* (P-count) density `σ`, with the smooth density shifted by
`δ = ρ − σ`.**  This is the form the low-density ledger consumes: the `F`-weight is evaluated at
`ρ` while the Jensen supply `½M₂mσ²` is read at `σ`, and the shift costs
`2cM₁mδ² + …` (the rows `(R1)`,`(R2)` of `FINDING_perSectorSmoothLowDens_session4.md` §4). -/
theorem meanFieldBalance_shift {M₁ M₂ μ σ δ c : ℝ} (hM₁ : 0 ≤ M₁) (hM : M₁ ≤ M₂) (hμ : 0 < μ)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 4) :
    2 * c * M₁ * (σ - μ) ^ 2 + μ * M₁ * σ - (1 / 2) * μ ^ 2 * M₁
      ≤ (1 / 2) * M₂ * σ ^ 2 := by
  have hsq : 0 ≤ (σ - μ) ^ 2 := sq_nonneg _
  have h3 : (1 / 2) * M₁ * (σ - μ) ^ 2 + μ * M₁ * σ - (1 / 2) * μ ^ 2 * M₁
      = (1 / 2) * M₁ * σ ^ 2 := by ring
  have h4 : 2 * c * (σ - μ) ^ 2 ≤ (1 / 2) * (σ - μ) ^ 2 := by nlinarith [hsq, hc, hc0]
  have h5 : 2 * c * M₁ * (σ - μ) ^ 2 ≤ (1 / 2) * M₁ * (σ - μ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hM₁]
  have h6 : (1 / 2) * M₁ * σ ^ 2 ≤ (1 / 2) * M₂ * σ ^ 2 := by
    nlinarith [sq_nonneg σ, hM]
  linarith [h5, h3, h6]

/-- **The low-density ledger (pure real) — the corrected `(LOWN)` route, background kept.**

Rows (all at the sector piece, `m = m_k`, `E = bErr`, `sbKin`, `sbPot`, `fibSum`, `pairSum` as in
`Work.BoseFixB1.sbPotHalvesBdd`):

* `(F)`  `X ≤ m·F(ρ) + 4·Ṽ` — the **sharp** `F`-row (`Work.BoseFixB1B.fWeight_taylorMean_of_bdd`,
  PROVED), `F(ρ) = μ(ρ−μ)²/(ρ+μ)`;
* `(fib)` `μ·fibSum ≤ μ·M₁·m·σ + W₁` — the **background half** of the ledger (`W₁ ≥ 0` the fibre's
  cross/`Q` excess over the `P`-part; the peel is PROVED as `sectorFibrePeelBdd`), instantiated with
  `W₁` its payable remainder;
* `(pair)` `½·pairSum ≥ ½·M₂·m·σ² − W₂` — the **pair half** (`W₂ ≥ 0` the defect of the pair sum
  below its `P`-part Jensen value `pairPPGeJensenBdd`, PROVED);
* `(split)` `sbPot = −μ·fibSum + ½·pairSum` — PROVED (`Work.BoseFixB1.sbPotHalvesBdd`);
* `(pay)` `4cM₁Ṽ + W₁ + W₂ + 4cM₁mδ² ≤ sbKin + C·E·m` — the **payables**, paid by the kinetic word
  (`Work.BoseFixB1.perBoxF_pieces.sbKin_ge_mu_av_cnPlus`, PROVED) and the error slot;
* `(Born)` `M₁ ≤ M₂` — the Born gap (PROVED: `Work.BoseFixB1S.w1MassB_le_flatPairMassB1`).

Conclusion: the low-density branch of the target, `c·M₁·X − ½μ²M₁m − C·E·m ≤ sbKin + sbPot`, for
`c ≤ 1/4`.  The Born gap is used in exactly one place (`meanFieldBalance_shift`), at `σ = μ`. -/
theorem lowCoreLedger {X m M₁ M₂ μ ρ σ δ Vv W₁ W₂ fibSum pairSum sbKin sbPot E c C : ℝ}
    (hM₁ : 0 ≤ M₁) (hM : M₁ ≤ M₂) (hμ : 0 < μ) (hm : 0 ≤ m) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 4)
    (hδ : δ = ρ - σ) (hρ0 : 0 ≤ ρ) (hVv : 0 ≤ Vv) (hW₁ : 0 ≤ W₁) (hW₂ : 0 ≤ W₂)
    (hF : X ≤ m * (μ * (ρ - μ) ^ 2 / (ρ + μ)) + 4 * Vv)
    (hfib : μ * fibSum ≤ μ * M₁ * m * σ + W₁)
    (hpair : (1 / 2) * pairSum ≥ (1 / 2) * M₂ * m * σ ^ 2 - W₂)
    (hsplit : sbPot = -(μ * fibSum) + (1 / 2) * pairSum)
    (hpay : 4 * c * M₁ * Vv + W₁ + W₂ + 4 * c * M₁ * m * δ ^ 2 ≤ sbKin + C * E * m) :
    c * M₁ * X - (1 / 2) * μ ^ 2 * M₁ * m - C * E * m ≤ sbKin + sbPot := by
  have hcM : 0 ≤ c * M₁ := mul_nonneg hc0 hM₁
  have hden : 0 < ρ + μ := by linarith
  -- the sharp `F`-row, and `F(ρ) ≤ (ρ−μ)² ≤ 2((σ−μ)² + δ²)`
  have hFρ : μ * (ρ - μ) ^ 2 / (ρ + μ) ≤ (ρ - μ) ^ 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg (ρ - μ), hμ, hρ0]
  have hshift : (ρ - μ) ^ 2 ≤ 2 * ((σ - μ) ^ 2 + δ ^ 2) := by
    rw [hδ]
    nlinarith [sq_nonneg ((ρ - σ) - (σ - μ))]
  have hA : c * M₁ * X ≤ c * M₁ * m * (2 * ((σ - μ) ^ 2 + δ ^ 2)) + 4 * (c * M₁) * Vv := by
    have h0 : c * M₁ * (m * (μ * (ρ - μ) ^ 2 / (ρ + μ)) + 4 * Vv)
        ≤ c * M₁ * (m * (2 * ((σ - μ) ^ 2 + δ ^ 2)) + 4 * Vv) := by
      apply mul_le_mul_of_nonneg_left _ hcM
      nlinarith [hFρ, hshift, hm, sq_nonneg (σ - μ), sq_nonneg δ]
    linarith [mul_le_mul_of_nonneg_left hF hcM, h0]
  -- the balance at `σ`, scaled by `m`
  have hbal := meanFieldBalance_shift (M₁ := M₁) (M₂ := M₂) (μ := μ) (σ := σ) (δ := δ)
    (c := c) hM₁ hM hμ hc0 hc
  have hbalm : m * (2 * c * M₁ * (σ - μ) ^ 2 + μ * M₁ * σ - (1 / 2) * μ ^ 2 * M₁)
      ≤ m * ((1 / 2) * M₂ * σ ^ 2) := mul_le_mul_of_nonneg_left hbal hm
  -- the payables
  have hpaym : 2 * c * M₁ * m * δ ^ 2 + 4 * c * M₁ * Vv + W₁ + W₂ ≤ sbKin + C * E * m := by
    have h2 : 0 ≤ 2 * c * M₁ * m * δ ^ 2 := by positivity
    linarith [hpay, h2]
  have bracket1 : 2 * c * M₁ * m * (σ - μ) ^ 2 + μ * M₁ * m * σ - (1 / 2) * μ ^ 2 * M₁ * m
      ≤ (1 / 2) * M₂ * m * σ ^ 2 := by nlinarith [hbalm]
  have hfib' : -(μ * M₁ * m * σ + W₁) ≤ -(μ * fibSum) := by linarith [hfib]
  rw [hsplit]
  linarith [hA, hfib', hpair, bracket1, hpaym]

end

end Work.BoseFixB1B

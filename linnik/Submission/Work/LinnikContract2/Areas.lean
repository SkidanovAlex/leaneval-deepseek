/-
# LinnikContract2 — Areas.lean  (**ROUND 2 FINAL, FROZEN**)

The areas of the Linnik `L = 5.5` contract, **round 2**.  Relative to round 1
(`Submission/Work/LinnikContract/Areas.lean`) the content is:

* `Area0 = WideMinExists` — **new, and proved.**  HB's §6 numbering `(6.1)`–`(6.2)` at height
  `10`: if some non-principal zero with `|Im| ≤ 10` exists then the `λ`-minimal such zero exists.
  This is a *theorem* of the development (`NumZero/exists_wideMin.lean`), so round 2 contains no
  unprovable input; it is kept as an area for bookkeeping and is **not** a hypothesis of `Area7`.
* `Area1`, `Area2`, `Area5`, `Area6` — **unchanged** (they do not mention `λ₁`'s minimality).
* `Area3` — unchanged *text*, but the hypothesis `IsMin1` now has the round-2 meaning
  (minimality over `|Im| ≤ 10`).  This is the input the `P₃` engine of HB §§6–10 needs
  (it drops `λ₁`-terms for every zero in the window `|Im u| ≤ 3 + δ`).
* `Area4` — the second conjunct (`D2`, HB Table 13 via Lemma 12.1) has its hypothesis
  **widened from `IsZ` to `IsZW`**: the hypothesis is `λ₁ ≥ e.1` for *every* non-principal zero
  of height `≤ 10`, which is HB §12's "either `|γ| ≥ 10` or `β ≤ 1 − 𝓛⁻¹λ₁`".  This is the
  defect reported in `.fm3_host/reports/lemma-LinnikAreas_area4.md`.
* `Area7` — the *same conclusion* as round 1, now with **no** setting clause: the numbered zero is
  supplied by the proved `Area0`, and the window `¬ IsZ χ₁ ρ₁` is closed by the five numerical
  certificates of `A7/WindowCert.lean` through the assembly `A7/WindowAssembly.lean`
  (`area7_window`).  (Round 2's earlier draft carried the setting clause `NumZeroNarrow`; it is
  now a theorem and has been deleted.)

Every area is a single `Prop`.  `rows15`/`rows14`/`table13` are the frozen round-1 tables,
transcribed literally (so they are *definitionally equal* to round 1's, see `Bridge.lean`).
-/
import Submission.Work.LinnikContract2.Defs

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikContract2

/-! ## AREA 0 — `WideMinExists`: the §6 numbered zero exists (and is *proved*) -/

/-- **HB's §6 numbered zero, existence form.**  For every `q`, if some non-principal zero of
height `≤ 10` exists then there is a pair `(χ₁,ρ₁)` with `IsMin1 χ₁ ρ₁`, i.e. `ρ₁` is a
non-principal zero of height `≤ 10` whose `λ` is minimal over that region.

This is a *theorem* of the development (`NumZero/exists_wideMin.lean`, `Numbering.lean`): the
region is finite, so `λ` attains its minimum.  It is recorded as an area only for bookkeeping —
`Assembly` does **not** take it as a hypothesis. -/
def WideMinExists : Prop :=
  ∀ (q : ℕ) [NeZero q],
    (∃ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ) →
    ∃ (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁

/-- **AREA 0** (proved: see `Work.LinnikContract2.area0`). -/
def Area0 : Prop := WideMinExists

/-! ## AREA 1 — `LBound13 ∧ LBoundSmall` (HB Lemma 2.5 = Burgess) -/

/-- HB Lemma 2.5 with φ = 1/3. -/
def LBound13 : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
        ‖LFunction χ ((σ:ℂ) + (t:ℂ) * I)‖ ≤
          Cb * (N:ℝ) ^ ((1/3:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|)

/-- HB Lemma 2.5, small-order case: φ = 1/4 when `ord χ ≤ log N` (HB Lemma 2.4). -/
def LBoundSmall : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ ε' : ℝ, 0 < ε' → ∃ Cb : ℝ, 0 < Cb ∧
    ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (orderOf χ : ℝ) ≤ Real.log N →
      ∀ σ t : ℝ, 1 - 1/(k:ℝ) ≤ σ → σ ≤ 1 + Real.log (Real.log (N:ℝ)) / Real.log (N:ℝ) →
        ‖LFunction χ ((σ:ℂ) + (t:ℂ) * I)‖ ≤
          Cb * (N:ℝ) ^ ((1/4:ℝ) * (1 - σ) * (1 + 1/(k:ℝ)) + ε') * (1 + |t|)

/-- **AREA 1.** -/
def Area1 : Prop := LBound13 ∧ LBoundSmall

/-! ## AREA 2 — `Reduction` (HB Lemmas 13.1–13.2; unchanged) -/

/-- **AREA 2.**  If the (signed) sum of `H((1-ρ)𝓛)` over the non-principal characters is bounded
away from `K² = (3/10)²`, then the progression contains a prime `≤ q^{11/2}`.
`R = R(ε)` and `q₀ = q₀(ε)` are uniform in `q` and `a`. -/
def Area2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (a : ℕ),
    a.Coprime q →
    (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
        ((starRingEnd ℂ) (χ a) * boxSum q (11/2) (3/10) R χ).re) < (3/10 : ℝ)^2 - ε →
    ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ (q : ℝ) ^ (11/2 : ℝ)

/-! ## AREA 3 — `ZeroFreeCert` (HB Theorems 1–3, Tables 8–10, Lemma 10.3, §14 rows) -/

/-- rows `(lo, hi, λ₀, λ₂, λ₃)`: HB Tables 8, 10, 9 (λ₃ capped below by 6/7), each lowered by
0.001 (literally round 1's table). -/
def rows15 : List (ℝ × ℝ × ℝ × ℝ × ℝ) :=
  [((348:ℝ)/1000, (36:ℝ)/100, (1308:ℝ)/1000, (902:ℝ)/1000, (1229:ℝ)/1000),
   ((36:ℝ)/100, (38:ℝ)/100, (1249:ℝ)/1000, (886:ℝ)/1000, (1180:ℝ)/1000),
   ((38:ℝ)/100, (4:ℝ)/10, (1195:ℝ)/1000, (870:ℝ)/1000, (1134:ℝ)/1000),
   ((4:ℝ)/10, (42:ℝ)/100, (1144:ℝ)/1000, (855:ℝ)/1000, (1093:ℝ)/1000),
   ((42:ℝ)/100, (44:ℝ)/100, (1098:ℝ)/1000, (841:ℝ)/1000, (1054:ℝ)/1000),
   ((44:ℝ)/100, (46:ℝ)/100, (1054:ℝ)/1000, (828:ℝ)/1000, (1017:ℝ)/1000),
   ((46:ℝ)/100, (48:ℝ)/100, (1014:ℝ)/1000, (815:ℝ)/1000, (983:ℝ)/1000),
   ((48:ℝ)/100, (5:ℝ)/10, (976:ℝ)/1000, (802:ℝ)/1000, (951:ℝ)/1000),
   ((5:ℝ)/10, (52:ℝ)/100, (940:ℝ)/1000, (790:ℝ)/1000, (921:ℝ)/1000),
   ((52:ℝ)/100, (54:ℝ)/100, (906:ℝ)/1000, (779:ℝ)/1000, (892:ℝ)/1000),
   ((54:ℝ)/100, (56:ℝ)/100, (874:ℝ)/1000, (768:ℝ)/1000, (865:ℝ)/1000),
   ((56:ℝ)/100, (58:ℝ)/100, (844:ℝ)/1000, (758:ℝ)/1000, (856:ℝ)/1000),
   ((58:ℝ)/100, (6:ℝ)/10, (815:ℝ)/1000, (748:ℝ)/1000, (856:ℝ)/1000)]

/-- rows `(lo, hi, c)` for `λ₁ < 0.348` (`χ₁, ρ₁` real): `min(λ₀,λ₂) ≥ c` (round 1's table). -/
def rows14 : List (ℝ × ℝ × ℝ) :=
  [((3:ℝ)/10, (348:ℝ)/1000, (127:ℝ)/100),
   ((25:ℝ)/100, (3:ℝ)/10, (141:ℝ)/100),
   ((2:ℝ)/10, (25:ℝ)/100, (158:ℝ)/100),
   (0, (2:ℝ)/10, (18:ℝ)/10)]

/-- **(Z1) HB Theorem 1.**  Below `λ₁ < 0.348`, the numbered zero `ρ₁` (the *wide* minimiser,
`IsMin1` — no working-region membership is assumed) is real and simple, belongs to a real
character `χ₁`, and it is the only zero of the *working region* with `λ < 0.348`.

Provability note: `ρ₁.im = 0` is HB Lemma 9.5/Theorem 1's conclusion for the §6 λ₁ (the engine's
window `|Im u| ≤ 3 + δ` is inside the wide region, which is why the hypothesis is the wide
`IsMin1`); its *consequence* `ρ₁ ∈ IsZ` is therefore derived, not assumed — which is precisely how
the working region re-enters the §§14–15 argument. -/
def Z1 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  lamOf q ρ₁ < 0.348 →
    χ₁ ^ 2 = 1 ∧ ρ₁.im = 0 ∧ zeroMult χ₁ ρ₁ = 1 ∧
      ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZ χ ρ → (χ ≠ χ₁ ∨ ρ ≠ ρ₁) → 0.348 ≤ lamOf q ρ

/-- **(Z2)** If `χ₁` is real and `ρ₁` is not, then `λ₁ ≥ 0.56`.
([X] Lemma 3.8 proves `0.628`; HB Lemma 9.5 only gives `0.518`, which is not enough.) -/
def Z2 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  χ₁ ^ 2 = 1 → ρ₁.im ≠ 0 → 0.56 ≤ lamOf q ρ₁

/-- **(Z3) The universal bounds**: HB Theorem 2 (`λ₀ ≥ 0.696`, `λ₂ ≥ 0.702`) and Lemma 10.3
(`λ₃ ≥ 6/7`), each lowered by `0.001`. -/
def Z3 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  Lam0Bound χ₁ ρ₁ 0.695 ∧ Lam2Bound χ₁ 0.701 ∧ Lam3Bound χ₁ 0.856

/-- **(Z4) The §15 rows**: for every row of `rows15` whose `λ₁`-interval contains `λ₁`, the three
bounds of that row hold. -/
def Z4 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) : Prop :=
  ∀ r ∈ rows15, r.1 ≤ lamOf q ρ₁ → lamOf q ρ₁ ≤ r.2.1 →
    Lam0Bound χ₁ ρ₁ r.2.2.1 ∧ Lam2Bound χ₁ r.2.2.2.1 ∧ Lam3Bound χ₁ r.2.2.2.2

/-- **(Z5) The §14 rows (Deuring–Heilbronn), plus the logarithmic repulsion.** -/
def Z5 {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ) (lamS : ℝ) : Prop :=
  (∀ r ∈ rows14, lamS ≤ lamOf q ρ₁ → r.1 ≤ lamOf q ρ₁ → lamOf q ρ₁ < r.2.1 →
      Lam0Bound χ₁ ρ₁ r.2.2 ∧ Lam2Bound χ₁ r.2.2) ∧
  (lamS ≤ lamOf q ρ₁ → lamOf q ρ₁ < 0.2 →
      Lam0Bound χ₁ ρ₁ ((99/100) * Real.log (1 / lamOf q ρ₁)) ∧
      Lam2Bound χ₁ ((99/100) * Real.log (1 / lamOf q ρ₁)))

/-- **AREA 3.**  Uniform (in `q`, above a threshold `q₀(lamS)`) zero-free-region data for the
numbered zero `ρ₁` of HB §6 — round-2 `IsMin1`, i.e. `λ(ρ₁)` is the minimum of `λ` over
`|Im| ≤ 10` (the numbered zero need not lie in `|Im| ≤ 1`).  All numerical bounds are explicit
rationals. -/
def ZeroFreeCert : Prop := ∀ lamS : ℝ, 0 < lamS → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
  (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ), IsMin1 χ₁ ρ₁ →
  Z1 χ₁ ρ₁ ∧ Z2 χ₁ ρ₁ ∧ Z3 χ₁ ρ₁ ∧ Z4 χ₁ ρ₁ ∧ Z5 χ₁ ρ₁ lamS

/-- **AREA 3.** -/
def Area3 : Prop := Area1 → ZeroFreeCert

/-! ## AREA 4 — `DensityCert` (HB Lemma 11.1 on the working region; HB Lemma 12.1 → Table 13) -/

/-- HB Table 13 as `(λ, column lower bound for λ₁, N₀)`; columns
`λ₁ = 0.348, 0.4, 0.44, 0.5, 0.58`, rows `λ = 0.800, …, 1.325`, exactly as printed
(round 1's table). -/
def table13 : List (ℝ × ℝ × ℕ) :=
  [((8:ℝ)/10, (348:ℝ)/1000, 8),  ((8:ℝ)/10, (4:ℝ)/10, 8),  ((8:ℝ)/10, (44:ℝ)/100, 8),
   ((8:ℝ)/10, (5:ℝ)/10, 7),      ((8:ℝ)/10, (58:ℝ)/100, 7),
   ((825:ℝ)/1000, (348:ℝ)/1000, 9), ((825:ℝ)/1000, (4:ℝ)/10, 9), ((825:ℝ)/1000, (44:ℝ)/100, 8),
   ((825:ℝ)/1000, (5:ℝ)/10, 8),  ((825:ℝ)/1000, (58:ℝ)/100, 8),
   ((85:ℝ)/100, (348:ℝ)/1000, 10), ((85:ℝ)/100, (4:ℝ)/10, 9), ((85:ℝ)/100, (44:ℝ)/100, 9),
   ((85:ℝ)/100, (5:ℝ)/10, 9),    ((85:ℝ)/100, (58:ℝ)/100, 8),
   ((875:ℝ)/1000, (348:ℝ)/1000, 11), ((875:ℝ)/1000, (4:ℝ)/10, 10), ((875:ℝ)/1000, (44:ℝ)/100, 10),
   ((875:ℝ)/1000, (5:ℝ)/10, 9),  ((875:ℝ)/1000, (58:ℝ)/100, 9),
   ((9:ℝ)/10, (348:ℝ)/1000, 12), ((9:ℝ)/10, (4:ℝ)/10, 11), ((9:ℝ)/10, (44:ℝ)/100, 11),
   ((9:ℝ)/10, (5:ℝ)/10, 10),     ((9:ℝ)/10, (58:ℝ)/100, 10),
   ((925:ℝ)/1000, (348:ℝ)/1000, 13), ((925:ℝ)/1000, (4:ℝ)/10, 12), ((925:ℝ)/1000, (44:ℝ)/100, 12),
   ((925:ℝ)/1000, (5:ℝ)/10, 11), ((925:ℝ)/1000, (58:ℝ)/100, 11),
   ((95:ℝ)/100, (348:ℝ)/1000, 15), ((95:ℝ)/100, (4:ℝ)/10, 14), ((95:ℝ)/100, (44:ℝ)/100, 13),
   ((95:ℝ)/100, (5:ℝ)/10, 12),   ((95:ℝ)/100, (58:ℝ)/100, 12),
   ((975:ℝ)/1000, (348:ℝ)/1000, 16), ((975:ℝ)/1000, (4:ℝ)/10, 15), ((975:ℝ)/1000, (44:ℝ)/100, 15),
   ((975:ℝ)/1000, (5:ℝ)/10, 14), ((975:ℝ)/1000, (58:ℝ)/100, 13),
   (1, (348:ℝ)/1000, 18),        (1, (4:ℝ)/10, 17), (1, (44:ℝ)/100, 16),
   (1, (5:ℝ)/10, 15),            (1, (58:ℝ)/100, 14),
   ((1025:ℝ)/1000, (348:ℝ)/1000, 21), ((1025:ℝ)/1000, (4:ℝ)/10, 19), ((1025:ℝ)/1000, (44:ℝ)/100, 18),
   ((1025:ℝ)/1000, (5:ℝ)/10, 17), ((1025:ℝ)/1000, (58:ℝ)/100, 15),
   ((105:ℝ)/100, (348:ℝ)/1000, 24), ((105:ℝ)/100, (4:ℝ)/10, 22), ((105:ℝ)/100, (44:ℝ)/100, 21),
   ((105:ℝ)/100, (5:ℝ)/10, 19),  ((105:ℝ)/100, (58:ℝ)/100, 17),
   ((1075:ℝ)/1000, (348:ℝ)/1000, 28), ((1075:ℝ)/1000, (4:ℝ)/10, 26), ((1075:ℝ)/1000, (44:ℝ)/100, 24),
   ((1075:ℝ)/1000, (5:ℝ)/10, 22), ((1075:ℝ)/1000, (58:ℝ)/100, 19),
   ((11:ℝ)/10, (348:ℝ)/1000, 34), ((11:ℝ)/10, (4:ℝ)/10, 30), ((11:ℝ)/10, (44:ℝ)/100, 28),
   ((11:ℝ)/10, (5:ℝ)/10, 25),    ((11:ℝ)/10, (58:ℝ)/100, 22),
   ((1125:ℝ)/1000, (348:ℝ)/1000, 42), ((1125:ℝ)/1000, (4:ℝ)/10, 36), ((1125:ℝ)/1000, (44:ℝ)/100, 33),
   ((1125:ℝ)/1000, (5:ℝ)/10, 29), ((1125:ℝ)/1000, (58:ℝ)/100, 25),
   ((115:ℝ)/100, (348:ℝ)/1000, 54), ((115:ℝ)/100, (4:ℝ)/10, 45), ((115:ℝ)/100, (44:ℝ)/100, 40),
   ((115:ℝ)/100, (5:ℝ)/10, 35),  ((115:ℝ)/100, (58:ℝ)/100, 29),
   ((1175:ℝ)/1000, (348:ℝ)/1000, 73), ((1175:ℝ)/1000, (4:ℝ)/10, 58), ((1175:ℝ)/1000, (44:ℝ)/100, 51),
   ((1175:ℝ)/1000, (5:ℝ)/10, 42), ((1175:ℝ)/1000, (58:ℝ)/100, 35),
   ((12:ℝ)/10, (348:ℝ)/1000, 111), ((12:ℝ)/10, (4:ℝ)/10, 81), ((12:ℝ)/10, (44:ℝ)/100, 67),
   ((12:ℝ)/10, (5:ℝ)/10, 54),    ((12:ℝ)/10, (58:ℝ)/100, 42),
   ((1225:ℝ)/1000, (348:ℝ)/1000, 218), ((1225:ℝ)/1000, (4:ℝ)/10, 127), ((1225:ℝ)/1000, (44:ℝ)/100, 97),
   ((1225:ℝ)/1000, (5:ℝ)/10, 71), ((1225:ℝ)/1000, (58:ℝ)/100, 53),
   ((125:ℝ)/100, (348:ℝ)/1000, 2583), ((125:ℝ)/100, (4:ℝ)/10, 279), ((125:ℝ)/100, (44:ℝ)/100, 166),
   ((125:ℝ)/100, (5:ℝ)/10, 104), ((125:ℝ)/100, (58:ℝ)/100, 70),
   ((1275:ℝ)/1000, (44:ℝ)/100, 520), ((1275:ℝ)/1000, (5:ℝ)/10, 184), ((1275:ℝ)/1000, (58:ℝ)/100, 100),
   ((13:ℝ)/10, (5:ℝ)/10, 667),   ((13:ℝ)/10, (58:ℝ)/100, 167),
   ((1325:ℝ)/1000, (58:ℝ)/100, 460)]

/-- **(D1) HB Lemma 11.1** with `φ = 1/3`, `c₁ = 1/10`, `c₂ = 1/4`, summed over the
non-principal characters with a zero in the working region of parameter `≤ λ₀ = (1/3)logloglog q`
(HB's `N(λ₀)` counts the *working-region* zeros: §11 defines `N(λ)` with `|t| ≤ 1`). -/
def D1 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
    ∑ χ ∈ Finset.univ.filter
        (fun χ : DirichletCharacter ℂ q => ∃ ρ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q),
      wHB (lamChar χ) ≤ 67/6 + ε

/-- **(D2) HB Table 13, from HB Lemma 12.1.**  Each row `e = (λ, λ₁-column, N₀)` states: if every
non-principal zero of height `≤ 10` has `λ ≥ e.2.1`, then `Ncount q e.1 ≤ e.2.2`.

The hypothesis is HB §12's *wide* form — "all zeros `ρ`, of any `L`-function to modulus `q`,
satisfy either `|γ| ≥ 10` or `β ≤ 1 − 𝓛⁻¹λ₁`" — and not the working-region form; the `N² − N`
off-diagonal terms of the Cauchy–Schwarz step of §12 sit at heights `γ⁽ʲ⁾ − γ⁽ᵏ⁾ ∈ [−2,2]`, whose
Lemma 5.2 windows (`|Im u| ≤ 3 + δ`) leave `|γ| ≤ 1`.  The conclusion counts the
*working-region* zeros (`Ncount`, as in HB's `N(λ)`).  `d2_hyp_of_isMin1` (`API.lean`) turns the
numbered pair `IsMin1` into this hypothesis. -/
def D2 : Prop :=
  ∀ e ∈ table13, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q],
    (∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), IsZW χ ρ → e.2.1 ≤ lamOf q ρ) →
    Ncount q e.1 ≤ e.2.2

/-- **AREA 4.** -/
def DensityCert : Prop := D1 ∧ D2

/-- **AREA 4.** -/
def Area4 : Prop := Area1 → DensityCert

/-! ## AREA 5 — `PerCharCert` (HB Lemma 13.3, uniform in λ; unchanged) -/

/-- **AREA 5.**  Per-character box sum bound: `Σ'_ρ ‖F₂((1-ρ)𝓛)‖ ≤ K²(B(λ) + η)` for every
character with no zero of `λ` below `lam` in the *working region*, uniformly in `λ ∈ [0,R]`.
(The region is `|γ| ≤ 1` in HB Lemma 13.2/13.3: the box is `1 - R/𝓛 ≤ β ≤ 1, |γ| ≤ R/𝓛`.) -/
def PerCharCert : Prop :=
  ∀ K : ℝ, 0 < K → K ≤ 1 → ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ lam : ℝ, 0 ≤ lam → lam ≤ R →
    (∀ ρ, IsZ χ ρ → lam ≤ lamOf q ρ) →
    boxAbs q K R χ ≤ K ^ 2 * (Bfun K lam + η)

/-- **AREA 5.** -/
def Area5 : Prop := Area1 → PerCharCert

/-! ## AREA 6 — `SiegelCase` ([HB90]; unchanged) -/

/-- **AREA 6.**  The Siegel-zero case: if a real zero with `λ ≤ lamS` exists and `q ≥ q₀(lamS)`,
the progression contains a prime `≤ q^{11/2}`. -/
def SiegelCase : Prop :=
  ∃ lamS : ℝ, 0 < lamS ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q], SiegelZero q lamS →
    ∀ a : ℕ, a.Coprime q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧ (p : ℝ) ≤ (q : ℝ) ^ (11/2 : ℝ)

/-- **AREA 6.** -/
def Area6 : Prop := SiegelCase

/-! ## AREA 7 — `Assembly` (HB §§14–15; unchanged conclusion) -/

-- **HB's §14/§15 setting, *discharged* (round 2, final).**
--
-- Round 2's earlier draft carried the setting clause
--
--   `NumZeroNarrow` : `IsMin1 χ₁ ρ₁ → (λ₁ < 348/1000 ∨ IsZ χ₁ ρ₁)`
--
-- (the wide minimiser either lies in the working region or is caught by the `§14` branch).  That
-- clause is now a **theorem**, not an input: in the window `¬ IsZ χ₁ ρ₁`, `(Z1)` forces
-- `λ₁ ≥ 348/1000`, and the §15 argument is then run at the *narrow* (working-region) minimiser,
-- with `A7/WindowCert.lean` (the five numerical certificates `win_g1`–`win_g5`) supplying the
-- numerical input and `A7/WindowAssembly.lean` (`area7_window`) the assembly.  The clause has
-- therefore been *deleted* from the contract.

/-- **AREA 7.**  Given the three certificates, and away from the Siegel case, the signed sum of
`H((1-ρ)𝓛)` is bounded away from `K² = (3/10)²` for all large `q`.  The numbered zero is supplied
internally by the *proved* `Area0` (`WideMinExists`); the numerical input is round 1's rational
certificate (`Submission.Work.LinnikContract.Numerics`) and, in the window `¬ IsZ χ₁ ρ₁`, the five
round-2 certificates `A7/WindowCert.lean` (worst total `9968/10000`, margin `0.0032`).
No setting clause is carried: the assembly is `A7/WindowAssembly.lean` (`area7_window`). -/
def Assembly : Prop :=
  ZeroFreeCert → DensityCert → PerCharCert →
  ∀ lamS : ℝ, 0 < lamS → ∃ η : ℝ, 0 < η ∧ ∀ R : ℝ, 0 < R → ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    ∀ [NeZero q],
    ¬ SiegelZero q lamS → ∀ a : ℕ, a.Coprime q →
    (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
        ((starRingEnd ℂ) (χ a) * boxSum q (11/2) (3/10) R χ).re) < (3/10 : ℝ)^2 - η

/-- **AREA 7.** -/
def Area7 : Prop := Assembly

end Work.LinnikContract2

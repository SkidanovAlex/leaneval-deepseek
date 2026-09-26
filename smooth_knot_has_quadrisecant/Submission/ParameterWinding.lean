import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.TrisecantStructure

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Parameter winding — advancing lifts of circle-valued families are surjective

Layer C (W) (the winding contradictions of the Pannwitz–Kuperberg endgame)
will need the following elementary fact about the *parameter circle* of a
knot.  Let `KnotParam = AddCircle period` be the parameter circle of the
knot.  The two winding cases of Kuperberg's argument concern a circular
component `C` of the trisecant locus; following the *middle point* of the
trisecants along `C` produces a continuous family `m : ℝ → KnotParam`
(parameterised by a real lift `t` of the circle `C`).  The case where `C`
winds twice around the Möbius band of secants has the property that, over
one circuit of `C`, the middle travels exactly once around the parameter
circle: in terms of a continuous real lift `G : ℝ → ℝ` of `m`
(`G t ↦ m t` under the quotient `ℝ → AddCircle period`) this says

    G (t + T) = G t + period          (hadv)

for the circuit length `T > 0`.  The content of this module:

* **`surj_of_lift_advance`** — the elementary consequence: any continuous
  real lift advancing by exactly `p` over time `T > 0` induces a
  *surjective* map `t ↦ (G t : AddCircle p)`.  Proof: fix a target class
  `x`, lift it to `r`; the function `H(t) = G t − r` is continuous with
  `H(T) = H(0) + p`, so by the intermediate value theorem on `[0,T]` the
  value `H` takes at `t` equals `k·p` for the integer `k = ⌊H(0)/p⌋ + 1`
  (the unique lattice point `p·ℤ` in the window `[H(0), H(0)+p]`); then
  `(G t : AddCircle p) = (r : AddCircle p) = x` because `k·p = 0` in the
  quotient by `zmultiples p`.

* **`knotParam_surj_of_lift_advance`** — the project instantiation with
  `p = period`: under the no-quadrisecant hypothesis the middle point of a
  secant class is a well-defined function of the class (`TrisecantCover`),
  so once Milestone 2 supplies a *twice-winding* circular family of
  trisecants, its middle lift advances by exactly `period` per circuit and
  hence **covers every knot parameter**.  Combined with the extremal
  lemma `TrisecantStructure.exists_uncovered_middle` (some parameter is
  *never* a strict middle) this gives Kuperberg's twice-winding
  contradiction — the covering of all parameters by a genuine middle map is
  impossible.

(The companion *once*-winding case — the jump discontinuity of the middle —
is a separate circle-order argument, recorded in ROADMAP.md as a later
Layer-C piece; it does not need this module.)

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-- `k·p` vanishes in the quotient `ℝ ⧸ zmultiples p`: adding an integer
multiple of the period to a real representative does not change the class. -/
lemma add_zsmul_period_eq_self (p : ℝ) (x : ℝ) (k : ℤ) :
    ((x + (k : ℝ) * p : ℝ) : AddCircle p) = (x : AddCircle p) := by
  calc
    ((x + (k : ℝ) * p : ℝ) : AddCircle p) =
        (x : AddCircle p) + (((k : ℝ) * p : ℝ) : AddCircle p) := by
      exact AddCircle.coe_add p x ((k : ℝ) * p)
    _ = (x : AddCircle p) + 0 := by
      congr 1
      rw [← zsmul_eq_mul]
      rw [AddCircle.coe_zsmul]
      rw [AddCircle.coe_period]
      simp
    _ = (x : AddCircle p) := by simp

/-- **Advancing lifts are surjective.**  Let `G : ℝ → ℝ` be continuous and
advance by exactly `p > 0` over every time interval of length `T > 0`:
`G (t + T) = G t + p`.  Then the induced circle-valued family
`t ↦ (G t : AddCircle p)` hits every class of the circle: over one circuit
the lift covers a full period, hence (intermediate value theorem) every
residue class modulo `p`.  This is the elementary core of the
twice-winding contradiction for the middle map of a trisecant family. -/
theorem surj_of_lift_advance {p T : ℝ} (hp : 0 < p) (hT : 0 < T)
    {G : ℝ → ℝ} (hG : Continuous G) (hadv : ∀ t, G (t + T) = G t + p) :
    Function.Surjective (fun t : ℝ => (G t : AddCircle p)) := by
  intro x
  rcases QuotientAddGroup.mk_surjective x with ⟨r, hr⟩
  let H : ℝ → ℝ := fun t => G t - r
  have hHc : Continuous H := hG.sub continuous_const
  let k : ℤ := Int.floor (H 0 / p) + 1
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hdiv : (H 0 / p) * p = H 0 := by field_simp [hp0]
  have hk1 : H 0 < (k : ℝ) * p := by
    have hlt := Int.lt_floor_add_one (H 0 / p)
    have hltm : (H 0 / p) * p < ((Int.floor (H 0 / p) : ℝ) + 1) * p := by
      exact mul_lt_mul_of_pos_right hlt hp
    have hkc : ((Int.floor (H 0 / p) : ℝ) + 1) = (k : ℝ) := by norm_num [k]
    simpa [hdiv, hkc] using hltm
  have hk2 : (k : ℝ) * p ≤ H 0 + p := by
    have hfl := Int.floor_le (H 0 / p)
    have hflm : (Int.floor (H 0 / p) : ℝ) * p ≤ (H 0 / p) * p := by
      exact mul_le_mul_of_nonneg_right hfl (le_of_lt hp)
    have hbase : (Int.floor (H 0 / p) : ℝ) * p ≤ H 0 := by simpa [hdiv] using hflm
    have hfl' : ((Int.floor (H 0 / p) : ℝ) + 1) * p ≤ H 0 + p := by
      calc ((Int.floor (H 0 / p) : ℝ) + 1) * p = (Int.floor (H 0 / p) : ℝ) * p + p := by ring
        _ ≤ H 0 + p := by
          simpa [add_comm] using (add_le_add_right hbase p)
    have hkc : ((Int.floor (H 0 / p) : ℝ) + 1) = (k : ℝ) := by norm_num [k]
    simpa [hkc] using hfl'
  have hGadv0 : G T = G 0 + p := by
    simpa using (hadv 0)
  have hHT : H T = H 0 + p := by
    dsimp [H]
    rw [hGadv0]
    ring
  have hkIcc : (k : ℝ) * p ∈ Set.Icc (H 0) (H T) := by
    rw [hHT]
    exact ⟨le_of_lt hk1, hk2⟩
  have hmem : (k : ℝ) * p ∈ H '' Set.Icc 0 T := by
    exact (intermediate_value_Icc (a := 0) (b := T) (le_of_lt hT) hHc.continuousOn) hkIcc
  rcases hmem with ⟨t, ht, ht'⟩
  refine ⟨t, ?_⟩
  change (G t : AddCircle p) = x
  have hGt : G t = r + (k : ℝ) * p := by
    dsimp [H] at ht'
    linarith
  rw [hGt]
  rw [add_zsmul_period_eq_self]
  exact hr

/-- **Project instantiation.**  For the knot parameter circle `AddCircle
period` (period = 2π), a continuous lift advancing by exactly one knot
period over a circuit of length `T > 0` covers *every* knot parameter.
This is the twice-winding middle-covering fact of the Pannwitz–Kuperberg
argument: it turns a twice-winding circular family of trisecants (whose
middle lift advances by `period` per circuit) into the surjectivity of the
middle map onto the parameter circle — contradicting
`TrisecantStructure.exists_uncovered_middle` once the family is known to
carry genuine middles. -/
theorem knotParam_surj_of_lift_advance {T : ℝ} (hT : 0 < T)
    {G : ℝ → ℝ} (hG : Continuous G) (hadv : ∀ t, G (t + T) = G t + period) :
    Function.Surjective (fun t : ℝ => (G t : AddCircle period)) := by
  exact surj_of_lift_advance period_pos hT hG hadv


/-- **Middle-surjectivity contradiction (the twice-winding endpoint).**
  Suppose a continuous middle family `t ↦ m t` (a real parametrisation of a
  circular component of the trisecant locus) covers *every* knot parameter
  (`Function.Surjective`) and each `m t` is a genuine middle point of some
  trisecant (`m t ∈ MiddleCovered r`).  Then every parameter would be a
  middle of some trisecant, contradicting the extremal lemma
  `TrisecantStructure.exists_uncovered_middle` (the point of the compact
  knot image farthest from a fixed centre is never strictly between two
  other knot points).  Combined with `knotParam_surj_of_lift_advance`, this
  is the contradiction that rules out the twice-winding circular component
  once Milestone 2 establishes that a twice-winding component yields a
  genuine middle family with an advancing lift. -/
theorem middle_surjective_contradiction {r : ℝ → Space} (h : IsSmoothKnot r)
    {m : ℝ → AddCircle period} (hmsurj : Function.Surjective m)
    (hmid : ∀ t, m t ∈ MiddleCovered r) : False := by
  rcases exists_uncovered_middle h with ⟨u, hu⟩
  rcases hmsurj u with ⟨t, ht⟩
  exact hu (by simpa [ht] using hmid t)


/-- **S247 — the TWICE-branch contradiction assembled (VERIFIED,
sorry-free)**: an advancing genuine-middle lift closes the twice-winding
contradiction by pure assembly — a continuous real lift `G` advancing by
a FULL period over every circuit of length `T` (`G (t + T) = G t +
period`, `0 < T`) whose circle values `(G t : AddCircle period)` are
genuine middles of trisecants (`∈ MiddleCovered r`, so the family is the
middle function of a twice-winding circular component) is impossible:
`knotParam_surj_of_lift_advance` (S78) makes `t ↦ (G t : AddCircle
period)` surjective, and `middle_surjective_contradiction` (S78) collides
the surjectivity with `TrisecantStructure.exists_uncovered_middle`
(Kuperberg's Lemma-compact: not every knot parameter is a middle).
  This is the analytic endpoint of the TWICE case: the family-production
lemma from the geometric TWICE data (the circular component chart,
L65 + `trisecantComponent_compactSide`, and the middle function along it
with full-period lift advance) supplies exactly the `G`/`hmid`
hypotheses; the contradiction then closes by this theorem with no further
analysis. -/
theorem twiceWinding_middle_contradiction {r : ℝ → Space} (h : IsSmoothKnot r)
    {T : ℝ} (hT : 0 < T) {G : ℝ → ℝ} (hG : Continuous G)
    (hadv : ∀ t, G (t + T) = G t + period)
    (hmid : ∀ t : ℝ, (G t : AddCircle period) ∈ MiddleCovered r) : False := by
  have hsurj : Function.Surjective (fun t : ℝ => (G t : AddCircle period)) :=
    knotParam_surj_of_lift_advance hT hG hadv
  exact middle_surjective_contradiction (r := r) h hsurj hmid

end LeanEval.KnotTheory.Quadrisecant

/-! ## S254 — integer-advancing lifts are surjective for ANY nonzero degree
(VERIFIED, sorry-free) — the `k ≠ 0` generalisation of
`surj_of_lift_advance` (sub-problem 5(a) of the S253b brick-(c)
decomposition)

The S253 degree fact (`componentMiddle_lift_advance`) gives the middle
selection on a circular component a real lift advancing by `(k : ℝ) *
period` for an integer `k` (the "degree"), and the S253b fallback plan for
the TWICE measurement is: the middle-surjectivity contradiction needs only
`k ≠ 0`, NOT the full-period `k = 1` of `TwiceWindingAdvancingLift`.  This
section therefore generalises the elementary advance lemma from exact
`p`-advance to advance by any nonzero integer multiple of `p`:

* **`int_in_unit_window`** — the lattice-point fact: any closed window
  `[a, a+1]` contains an integer (the floor argument, `p = 1` form);
* **`surj_of_lift_advance_zsmul`** — THE generalisation: a continuous
  `G : ℝ → ℝ` with `G (t + T) = G t + (k : ℝ) * p`, `0 < p`, `0 < T`,
  `k ≠ 0`, induces a surjective `t ↦ (G t : AddCircle p)`.  Proof: scale
  by `p` (work with `F t = (G t − r)/p` so the advance is exactly the
  integer `k`); over one circuit the window `[F 0, F T]` has integer
  length `|k| ≥ 1`, so it contains an integer `m` (in the `k > 0` branch
  the unit window below `F 0`, in the `k < 0` branch the one below
  `⌊F 0⌋`), and the intermediate value theorem (ordinary / reversed
  `intermediate_value_Icc'`) finds `t` with `F t = m`, i.e.
  `G t = r + (m : ℝ) * p` — a representative of the target class;
* **`knotParam_surj_of_lift_advance_zsmul`** — the project instantiation
  with `p = period`;
* **`twiceWinding_middle_contradiction_zsmul`** — the S247
  `twiceWinding_middle_contradiction` mirror for ANY nonzero degree: an
  advancing genuine-middle lift with `k ≠ 0` already contradicts
  `exists_uncovered_middle` (the TWICE branch needs only nonzero degree,
  not degree ±1 — S253b sub-problem 5(b), the fallback simplification of
  the winding measurement).

STATUS after S254: the fallback TWICE contradiction is verified at the
pure-assembly level: a circular component whose middle selection has any
nonzero integer degree (real lift advancing by `(k : ℝ) * period`, `k ≠ 0`)
is impossible — the measurement needed from the twice-winding geometry is
`k ≠ 0` ("μ∘χ is not null-homotopic"), strictly weaker than the `k = 1`
full-period advance of `TwiceWindingAdvancingLift` (S253).  The
component-level assembly `no_twiceWinding_component_of_lift_zsmul` is in
ComponentWindingData (S254).  Tree green; TWO documented sorries; no
children pending.
-/

namespace LeanEval.KnotTheory.Quadrisecant


/-- **The unit-window lattice-point lemma (VERIFIED)**: any closed real
window `[a, a+1]` contains an integer.  (The `p = 1` form of the window
lemma used by `surj_of_lift_advance_zsmul`; `m = ⌊a⌋ + 1` lies strictly
above `a` — `Int.lt_floor_add_one` — and at most `a + 1` —
`Int.floor_le`.) -/
lemma int_in_unit_window (a : ℝ) : ∃ m : ℤ, a ≤ (m : ℝ) ∧ (m : ℝ) ≤ a + 1 := by
  refine ⟨Int.floor a + 1, ?_, ?_⟩
  · have h1 := Int.lt_floor_add_one a
    have hm : ((Int.floor a : ℝ) + 1) = ((Int.floor a + 1 : ℤ) : ℝ) := by norm_num
    calc a ≤ (Int.floor a : ℝ) + 1 := le_of_lt h1
      _ = ((Int.floor a + 1 : ℤ) : ℝ) := hm
  · have h2 := Int.floor_le a
    calc ((Int.floor a + 1 : ℤ) : ℝ) = (Int.floor a : ℝ) + 1 := by norm_num
      _ ≤ a + 1 := by linarith

/-- **Surjectivity of integer-advancing lifts, any nonzero degree
(VERIFIED)**: let `G : ℝ → ℝ` be continuous and advance by the nonzero
integer multiple `k` of the period `p > 0` over every time interval of
length `T > 0`: `G (t + T) = G t + (k : ℝ) * p`.  Then the circle-valued
family `t ↦ (G t : AddCircle p)` is surjective: over one circuit the lift
covers `|k| ≥ 1` full periods, so (intermediate value theorem, after
scaling by `p` so the window endpoints differ by the integer `k`) every
residue class modulo `p` is attained.  This is the `k ≠ 0` generalisation
of `surj_of_lift_advance` — the S253b fallback measurement of the
twice-winding middle (only nonzero degree is needed, not degree ±1). -/
theorem surj_of_lift_advance_zsmul {p T : ℝ} (hp : 0 < p) (hT : 0 < T)
    {k : ℤ} (hk : k ≠ 0) {G : ℝ → ℝ} (hG : Continuous G)
    (hadv : ∀ t : ℝ, G (t + T) = G t + (k : ℝ) * p) :
    Function.Surjective (fun t : ℝ => (G t : AddCircle p)) := by
  intro x
  rcases QuotientAddGroup.mk_surjective x with ⟨r, hr⟩
  let F : ℝ → ℝ := fun t => (G t - r) / p
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hFc : Continuous F :=
    (hG.sub continuous_const).div continuous_const (fun _ => hp0)
  have hFT : F T = F 0 + (k : ℝ) := by
    dsimp [F]
    calc
      (G T - r) / p = (G 0 + (k : ℝ) * p - r) / p := by
        have hGadv0 : G T = G 0 + (k : ℝ) * p := by simpa using (hadv 0)
        rw [hGadv0]
      _ = (G 0 - r) / p + (k : ℝ) := by
        field_simp [hp0]
        ring
  rcases lt_or_gt_of_ne hk with hkn | hkp
  · -- k < 0: window [F 0 + k, F 0] contains ⌊F 0⌋
    have hk1 : (k : ℝ) ≤ -1 := by
      have hz : k + 1 ≤ 0 := Int.add_one_le_iff.mpr hkn
      have hz' : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast hz
      linarith
    let m : ℤ := Int.floor (F 0)
    have hm1 : F 0 - 1 < (m : ℝ) := by
      have h1 := Int.lt_floor_add_one (F 0)
      dsimp [m] at h1 ⊢
      linarith
    have hm2 : (m : ℝ) ≤ F 0 := by
      dsimp [m]
      exact Int.floor_le (F 0)
    have hwin : (m : ℝ) ∈ Set.Icc (F T) (F 0) := by
      have hFTlo : F T ≤ (m : ℝ) := by
        rw [hFT]
        have h1 : F 0 + (k : ℝ) ≤ F 0 - 1 := by linarith
        exact le_trans h1 (le_of_lt hm1)
      exact ⟨hFTlo, hm2⟩
    rcases (intermediate_value_Icc' (a := 0) (b := T) (le_of_lt hT) hFc.continuousOn) hwin with
      ⟨t, ht, hFt⟩
    refine ⟨t, ?_⟩
    change (G t : AddCircle p) = x
    have hFval : F t = (m : ℝ) := hFt
    have hGt : G t = r + (m : ℝ) * p := by
      have hmm := congrArg (fun z : ℝ => z * p) hFval
      dsimp [F] at hmm
      have hmm' : (G t - r) = (m : ℝ) * p := by
        field_simp [hp0] at hmm ⊢
        linarith
      linarith
    rw [hGt]
    rw [add_zsmul_period_eq_self]
    exact hr
  · -- 0 < k: window [F 0, F 0 + k] contains ⌊F 0⌋ + 1
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
      have hz : 1 ≤ k := Int.add_one_le_iff.mpr hkp
      exact_mod_cast hz
    let m : ℤ := Int.floor (F 0) + 1
    have hm1 : F 0 ≤ (m : ℝ) := by
      have h1 := Int.lt_floor_add_one (F 0)
      have hmc : ((Int.floor (F 0) : ℝ) + 1) = (m : ℝ) := by dsimp [m]; norm_num
      calc F 0 ≤ (Int.floor (F 0) : ℝ) + 1 := le_of_lt h1
        _ = (m : ℝ) := hmc
    have hm2 : (m : ℝ) ≤ F 0 + 1 := by
      have h2 := Int.floor_le (F 0)
      have hmc : ((Int.floor (F 0) : ℝ) + 1) = (m : ℝ) := by dsimp [m]; norm_num
      calc (m : ℝ) = (Int.floor (F 0) : ℝ) + 1 := hmc.symm
        _ ≤ F 0 + 1 := by linarith
    have hwin : (m : ℝ) ∈ Set.Icc (F 0) (F T) := by
      have hup : (m : ℝ) ≤ F T := by
        rw [hFT]
        exact le_trans hm2 (by linarith)
      exact ⟨hm1, hup⟩
    rcases (intermediate_value_Icc (a := 0) (b := T) (le_of_lt hT) hFc.continuousOn) hwin with
      ⟨t, ht, hFt⟩
    refine ⟨t, ?_⟩
    change (G t : AddCircle p) = x
    have hFval : F t = (m : ℝ) := hFt
    have hGt : G t = r + (m : ℝ) * p := by
      have hmm := congrArg (fun z : ℝ => z * p) hFval
      dsimp [F] at hmm
      have hmm' : (G t - r) = (m : ℝ) * p := by
        field_simp [hp0] at hmm ⊢
        linarith
      linarith
    rw [hGt]
    rw [add_zsmul_period_eq_self]
    exact hr

/-- **Project instantiation (any nonzero degree, VERIFIED)**: for the knot
parameter circle `AddCircle period` (period = 2π), a continuous lift
advancing by the nonzero integer multiple `k` of one knot period over a
circuit of length `T > 0` covers every knot parameter.  This is the
`k ≠ 0` generalisation of `knotParam_surj_of_lift_advance`. -/
theorem knotParam_surj_of_lift_advance_zsmul {T : ℝ} (hT : 0 < T) {k : ℤ} (hk : k ≠ 0)
    {G : ℝ → ℝ} (hG : Continuous G) (hadv : ∀ t : ℝ, G (t + T) = G t + (k : ℝ) * period) :
    Function.Surjective (fun t : ℝ => (G t : AddCircle period)) := by
  exact surj_of_lift_advance_zsmul period_pos hT hk hG hadv

/-- **Middle-surjectivity contradiction, any nonzero degree (VERIFIED)**:
a continuous genuine-middle family `t ↦ (G t : AddCircle period)` whose
real lift advances by the nonzero integer multiple `k` of the knot period
(`G (t + T) = G t + (k : ℝ) * period`, `0 < T`) is impossible:
`knotParam_surj_of_lift_advance_zsmul` makes the family surjective and
`middle_surjective_contradiction` collides it with
`TrisecantStructure.exists_uncovered_middle`.  This is the S247 endpoint
generalised to any nonzero degree — the S253b fallback that the
twice-winding measurement only needs `k ≠ 0` (that `μ∘χ` is not
null-homotopic on the component), not the exact `k = ±1`. -/
theorem twiceWinding_middle_contradiction_zsmul {r : ℝ → Space} (h : IsSmoothKnot r)
    {T : ℝ} (hT : 0 < T) {k : ℤ} (hk : k ≠ 0) {G : ℝ → ℝ} (hG : Continuous G)
    (hadv : ∀ t : ℝ, G (t + T) = G t + (k : ℝ) * period)
    (hmid : ∀ t : ℝ, (G t : AddCircle period) ∈ MiddleCovered r) : False := by
  have hsurj : Function.Surjective (fun t : ℝ => (G t : AddCircle period)) :=
    knotParam_surj_of_lift_advance_zsmul hT hk hG hadv
  exact middle_surjective_contradiction (r := r) h hsurj hmid

end LeanEval.KnotTheory.Quadrisecant

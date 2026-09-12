import Mathlib
import Submission.Work.Lattice.AlignedBases
import Submission.Work.Lattice.IntrinsicIndex
import Submission.Work.Polygon.ConvexRankEquation
import Submission.Commons.Lattice.Counting.grassmann_codim_incomparable
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_concat_le
import Submission.Commons.LinearAlgebra.Submodule.realSpan_inf_eq_of_saturated_discrete

/-!
# The `φ`-slack and the compatibility of tight realisers (P2-general HN-flag core)

The paper's §3 Harder–Narasimhan layer is built from the **slacked value**

    `φ_A(W) = log covol(W) + A · dim W · (d − dim W)`      (`A > 0`)

on the saturated subgroups `W` of a full-rank lattice `Λ ≤ ℝᵈ` (`latticeCovol` = the
covolume of `W` inside its own real span, `dim W = subDim W` = the `ℝ`-rank).

This module proves the two structural facts that make the HN flag exist (instead of
citing it), in the Euclidean form where the norm-equivalence constant `A₂` of the paper
vanishes and any `A > 0` gives a *strict* slack:

1. **Submodularity with slack.**  For saturated `V, W ≤ Λ` which are **incomparable**,

       `φ_A(V⊓W) + φ_A(V⊔W) + 2A ≤ φ_A(V) + φ_A(W)`.

   Ingredients: the log-covol **submodularity** for saturated pairs (proven in
   `AlignedBases`, both the `V ⊓ W ≠ ⊥` case via the aligned-basis exterior engine and
   the transverse `V ⊓ W = ⊥` case proven here via `exteriorPower_norm_concat_le`), the
   **rank additivity** `dim(V⊓W) + dim(V⊔W) = dim V + dim W` of saturated pairs (from the
   Commons real-span intersection formula `realSpan_inf_eq_of_saturated_discrete`), and
   the elementary counting inequality `grassmann_codim_incomparable` (L49) for the
   quadratic term.

2. **Compatibility of tight realisers.**  Let `c` be a **discrete-convex** function on
   `{0,…,d}` lying below the `φ_A`-data (`c (dim X) ≤ φ_A(X)` for the subgroups at hand).
   If two saturated subgroups `V, W` are **tight** (`φ_A(V) = c (dim V)`,
   `φ_A(W) = c (dim W)`), then `V` and `W` are **comparable** (`V ≤ W` or `W ≤ V`).

   Indeed, incomparability would give, with `m = dim(V⊓W) < min(dim V, dim W)` and
   `n = dim(V⊔W) > max(dim V, dim W)` and the rank equation `m + n = dim V + dim W`:
   submodularity + slack, `c ≤` data and tightness combine into
   `c m + c n ≤ c (dim V) + c (dim W) − 2A`, while the reverse convexity along the rank
   equation (`convex_rank_equation`) gives `c m + c n ≥ c (dim V) + c (dim W)` —
   contradiction for `A > 0`.

Consequences recorded: realisers of the same rank coincide, hence the tight subgroups of
`Λ` form a **chain** under inclusion — the skeleton of the Harder–Narasimhan filtration.

All declarations are Mathlib + Submission (`AlignedBases`, `IntrinsicIndex`,
`ConvexRankEquation`) + the Commons lemmas L49 / L52 / `realSpan_inf_eq_of_saturated_discrete`.
-/

noncomputable section

open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Submission.PhiSlack

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.IntrinsicIndex
open Submission.MixedRankSpectrum
open Submission.LatticePolygon

/-- **Saturation in hull form**: `Saturated Λ V` (`V = hull Λ V`) is equivalent to the
pointwise characterisation `x ∈ V ↔ x ∈ Λ ∧ x ∈ realSpan V`. -/
lemma saturated_iff {d : ℕ} (Λ V : Submodule ℤ (E d)) :
    Saturated Λ V ↔ ∀ x : E d, x ∈ V ↔ x ∈ Λ ∧ x ∈ realSpan V := by
  constructor
  · intro h x
    conv_lhs => rw [h]
    exact hull_mem_iff Λ V x
  · intro h
    dsimp [Saturated]
    apply le_antisymm
    · intro x hx
      exact (hull_mem_iff Λ V x).mpr ((h x).mp hx)
    · intro x hx
      exact (h x).mpr ((hull_mem_iff Λ V x).mp hx)

/-- The real span of a join is the join of the real spans. -/
lemma realSpan_sup {d : ℕ} (V W : Submodule ℤ (E d)) :
    realSpan (V ⊔ W) = realSpan V ⊔ realSpan W := by
  apply le_antisymm
  · rw [realSpan, Submodule.span_le]
    intro x hx
    obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.subset_span (s := (V : Set (E d))) hv))
      (Submodule.mem_sup_right (Submodule.subset_span (s := (W : Set (E d))) hw))
  · exact sup_le
      (Submodule.span_mono (by intro x hx; exact Submodule.mem_sup_left hx))
      (Submodule.span_mono (by intro x hx; exact Submodule.mem_sup_right hx))

/-- **Rank additivity of saturated pairs**: for saturated `V, W ≤ Λ` (a full-rank
lattice, so that `Λ` is discrete), `dim(V⊓W) + dim(V⊔W) = dim V + dim W`. -/
theorem subDim_inf_add_subDim_sup {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) :
    subDim (V ⊓ W) + subDim (V ⊔ W) = subDim V + subDim W := by
  have hVform := (saturated_iff Λ V).mp hVsat
  have hWform := (saturated_iff Λ W).mp hWsat
  have hL87 :=
    Commons.LinearAlgebra.Submodule.realSpan_inf_eq_of_saturated_discrete Λ V W hVform hWform
  have hsup := realSpan_sup V W
  have hR := Submodule.finrank_sup_add_finrank_inf_eq (realSpan V) (realSpan W)
  rw [← hsup] at hR
  have hL87' : realSpan V ⊓ realSpan W = realSpan (V ⊓ W) := hL87
  rw [hL87'] at hR
  simp only [subDim]
  omega

/-- **Strict rank drop of a saturated pair**: a proper meet of saturated subgroups has
strictly smaller rank. -/
lemma subDim_inf_lt_of_ne {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hne : V ⊓ W ≠ V) :
    subDim (V ⊓ W) < subDim V := by
  by_contra hcon
  have hcon' : subDim V ≤ subDim (V ⊓ W) := not_lt.mp hcon
  have hle : subDim (V ⊓ W) ≤ subDim V :=
    Submodule.finrank_mono (Submodule.span_mono (by intro x hx; exact hx.1))
  have hfin : subDim (V ⊓ W) = subDim V := le_antisymm hle hcon'
  have hspanle : realSpan (V ⊓ W) ≤ realSpan V :=
    Submodule.span_mono (by intro x hx; exact hx.1)
  have heq : realSpan (V ⊓ W) = realSpan V :=
    Submodule.eq_of_le_of_finrank_eq hspanle (by simpa [subDim] using hfin)
  have hh : hull Λ (V ⊓ W) = hull Λ V := by
    ext x
    rw [hull_mem_iff, hull_mem_iff, heq]
  have h1 : V ⊓ W = hull Λ (V ⊓ W) := saturated_inf Λ V W hVsat hWsat
  exact hne (by rw [h1, hh]; exact hVsat.symm)

/-- The span of the concatenation of two families is the join of their spans. -/
lemma span_append_eq_sup {M : Type*} [AddCommGroup M] [Module ℤ M] {p q : ℕ}
    (u : Fin p → M) (v : Fin q → M) :
    Submodule.span ℤ (Set.range (Fin.append u v)) =
      Submodule.span ℤ (Set.range u) ⊔ Submodule.span ℤ (Set.range v) := by
  rw [Submission.AlignedBases.range_append, Submodule.span_union]

/-- **The transverse case of log-covol submodularity**: for saturated `V, W ≤ Λ` with
`V ⊓ W = ⊥` (in particular disjoint in their real spans),

`log covol(V⊔W) ≤ log covol V + log covol W`.

Proof: take `ℤ`-basis families `cV`, `cW` of `V`, `W`; their concatenation is `ℤ`- and
`ℝ`-independent and spans `V ⊔ W` (since the meet is trivial), and every covolume is the
norm of the corresponding `ιMulti` (`latticeCovol_span`), so the claim is the Commons
concatenation inequality `exteriorPower_norm_concat_le` in logarithmic form. -/
theorem logCovol_sup_le_add_of_inf_bot {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hbot : V ⊓ W = ⊥) :
    Real.log (latticeCovol (V ⊔ W)) ≤
      Real.log (latticeCovol V) + Real.log (latticeCovol W) := by
  classical
  by_cases hV0 : V = ⊥
  · subst hV0
    rw [bot_sup_eq, logCovol_bot, zero_add]
  by_cases hW0 : W = ⊥
  · subst hW0
    rw [sup_bot_eq, logCovol_bot, add_zero]
  have hVle : V ≤ Λ := saturated_le Λ V hVsat
  have hWle : W ≤ Λ := saturated_le Λ W hWsat
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin V hVle hV0 with
    ⟨cV, hliRV, hzliV, hmemV, hVspan⟩
  rcases exists_basis_family_int_of_le_lattice (d := d) Λ hΛfin W hWle hW0 with
    ⟨cW, hliRW, hzliW, hmemW, hWspan⟩
  have hsubV : 0 < subDim V := Nat.pos_of_ne_zero fun hz => hV0 ((subDim_eq_zero_iff_bot V).mp hz)
  have hsubW : 0 < subDim W := Nat.pos_of_ne_zero fun hz => hW0 ((subDim_eq_zero_iff_bot W).mp hz)
  have hzliComb : LinearIndependent ℤ (Fin.append cV cW) :=
    Submission.AlignedBases.zli_append2 cV cW V W hzliV hzliW hVspan hWspan hbot
  have hspanComb : Submodule.span ℤ (Set.range (Fin.append cV cW)) = V ⊔ W := by
    rw [span_append_eq_sup, ← hVspan, ← hWspan]
  have hmemComb : ∀ r : Fin (subDim V + subDim W), (Fin.append cV cW) r ∈ (Λ : Set (E d)) := by
    intro r
    rcases Submission.AlignedBases.fin_eq_castAdd_or_natAdd (m := subDim V) (a := subDim W) r with
      ⟨i, rfl⟩ | ⟨k, rfl⟩
    · rw [Fin.append_left]
      exact hmemV i
    · rw [Fin.append_right]
      exact hmemW k
  have hliRComb : LinearIndependent ℝ (Fin.append cV cW) :=
    linearIndependent_real_of_mem_lattice (d := d) Λ hΛfin _ hmemComb hzliComb
  have hcovV : latticeCovol V = ‖exteriorPower.ιMulti ℝ (subDim V) cV‖ := by
    conv_lhs => rw [hVspan]
    exact latticeCovol_span hsubV cV hliRV
  have hcovW : latticeCovol W = ‖exteriorPower.ιMulti ℝ (subDim W) cW‖ := by
    conv_lhs => rw [hWspan]
    exact latticeCovol_span hsubW cW hliRW
  have hcovS : latticeCovol (V ⊔ W) =
      ‖exteriorPower.ιMulti ℝ (subDim V + subDim W) (Fin.append cV cW)‖ := by
    conv_lhs => rw [← hspanComb]
    exact latticeCovol_span (by omega) (Fin.append cV cW) hliRComb
  have hprod : latticeCovol (V ⊔ W) ≤ latticeCovol V * latticeCovol W := by
    rw [hcovS, hcovV, hcovW]
    exact Commons.Analysis.InnerProductSpace.exteriorPower_norm_concat_le cV cW
  have hposV : 0 < latticeCovol V := by
    rw [hcovV]
    exact norm_pos_iff.mpr
      (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent cV hliRV)
  have hposW : 0 < latticeCovol W := by
    rw [hcovW]
    exact norm_pos_iff.mpr
      (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent cW hliRW)
  have hposS : 0 < latticeCovol (V ⊔ W) := by
    rw [hcovS]
    exact norm_pos_iff.mpr
      (Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent _ hliRComb)
  have h := Real.log_le_log hposS hprod
  rwa [Real.log_mul hposV.ne' hposW.ne'] at h

/-- **Log-covol submodularity for saturated pairs, both cases**: for saturated
`V, W ≤ Λ` (no hypothesis on the meet),

`log covol(V⊓W) + log covol(V⊔W) ≤ log covol V + log covol W`. -/
theorem logCovol_submodularity_saturated_general {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) :
    Real.log (latticeCovol (V ⊓ W)) + Real.log (latticeCovol (V ⊔ W)) ≤
      Real.log (latticeCovol V) + Real.log (latticeCovol W) := by
  by_cases hN0 : V ⊓ W = ⊥
  · rw [hN0, logCovol_bot, zero_add]
    exact logCovol_sup_le_add_of_inf_bot Λ V W hΛfin hVsat hWsat hN0
  · have hV0 : V ≠ ⊥ := fun h => hN0 (by rw [h, bot_inf_eq])
    have hW0 : W ≠ ⊥ := fun h => hN0 (by rw [h, inf_bot_eq])
    exact Submission.AlignedBases.logCovol_submodularity_saturated Λ V W hΛfin
      (saturated_le Λ V hVsat) (saturated_le Λ W hWsat) hV0 hW0 hVsat hWsat hN0

/-- **The slacked Grayson value** `φ_A(W) = log covol(W) + A · dim W · (d − dim W)`. -/
noncomputable def phi {d : ℕ} (A : ℝ) (W : Submodule ℤ (E d)) : ℝ :=
  Real.log (latticeCovol W) + A * ((subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ)))

/-- **The quadratic-term slack in the incomparable case** (Lemma 3 / L49, rank form):
for saturated incomparable `V, W ≤ Λ`,

`m(d−m) + n(d−n) + 2 ≤ k(d−k) + ℓ(d−ℓ)`,  `m = dim(V⊓W)`, `n = dim(V⊔W)`,
`k = dim V`, `ℓ = dim W`. -/
theorem quad_codim_slack {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hmk : subDim (V ⊓ W) < subDim V) (hmℓ : subDim (V ⊓ W) < subDim W) :
    (subDim V : ℝ) * ((d : ℝ) - (subDim V : ℝ)) +
        (subDim W : ℝ) * ((d : ℝ) - (subDim W : ℝ)) ≥
      (subDim (V ⊓ W) : ℝ) * ((d : ℝ) - (subDim (V ⊓ W) : ℝ)) +
        (subDim (V ⊔ W) : ℝ) * ((d : ℝ) - (subDim (V ⊔ W) : ℝ)) + 2 := by
  have hadd := subDim_inf_add_subDim_sup Λ V W hVsat hWsat
  have hle : subDim (V ⊓ W) ≤ subDim V + subDim W := by omega
  have hmn : (subDim (V ⊔ W) : ℝ) =
      (subDim V : ℝ) + (subDim W : ℝ) - (subDim (V ⊓ W) : ℝ) := by
    have h1 : subDim (V ⊔ W) = subDim V + subDim W - subDim (V ⊓ W) := by omega
    rw [h1, Nat.cast_sub hle]
    push_cast
    ring
  have hx : (subDim (V ⊓ W) : ℝ) + 1 ≤ (subDim V : ℝ) := by
    have : subDim (V ⊓ W) + 1 ≤ subDim V := hmk
    exact_mod_cast this
  have hy : (subDim (V ⊓ W) : ℝ) + 1 ≤ (subDim W : ℝ) := by
    have : subDim (V ⊓ W) + 1 ≤ subDim W := hmℓ
    exact_mod_cast this
  have h49 := Commons.Lattice.Counting.grassmann_codim_incomparable (subDim V : ℝ)
    (subDim W : ℝ) (subDim (V ⊓ W) : ℝ) (d : ℝ) hx hy
  rw [← hmn] at h49
  linarith [h49]

/-- **Submodularity with slack** (the paper's Lemma 3, Euclidean/no-norm-equivalence
form): for **incomparable** saturated `V, W ≤ Λ`,

`φ_A(V⊓W) + φ_A(V⊔W) + 2A ≤ φ_A(V) + φ_A(W)`. -/
theorem phi_incomparable_slack {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    {A : ℝ} (hA : 0 < A) (hVsat : Saturated Λ V) (hWsat : Saturated Λ W)
    (hinc : ¬ (V ≤ W) ∧ ¬ (W ≤ V)) :
    phi A V + phi A W ≥ phi A (V ⊓ W) + phi A (V ⊔ W) + 2 * A := by
  have hmk : subDim (V ⊓ W) < subDim V :=
    subDim_inf_lt_of_ne Λ V W hVsat hWsat (fun h => hinc.1 (inf_eq_left.mp h))
  have hmℓ : subDim (V ⊓ W) < subDim W := by
    simpa [inf_comm] using subDim_inf_lt_of_ne Λ W V hWsat hVsat
      (fun h => hinc.2 (inf_eq_left.mp h))
  have hsub := logCovol_submodularity_saturated_general Λ V W hΛfin hVsat hWsat
  have hslack := quad_codim_slack Λ V W hVsat hWsat hmk hmℓ
  simp only [phi]
  nlinarith [hsub, hslack, hA]

/-- **Compatibility of tight realisers** (the HN-flag key step).  Let `c` be
discrete-convex on `{0,…,d}` and below the `φ_A`-data (`c (dim X) ≤ φ_A X` at `V⊓W` and
`V⊔W`).  If the saturated subgroups `V, W ≤ Λ` are tight (`φ_A V = c (dim V)`,
`φ_A W = c (dim W)`), then `V` and `W` are comparable. -/
theorem comparable_of_tight {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) {c : ℕ → ℝ}
    (hcvx : Submission.Polygon.DiscreteConvexOn c d)
    (hVtight : phi A V = c (subDim V)) (hWtight : phi A W = c (subDim W))
    (hinf : c (subDim (V ⊓ W)) ≤ phi A (V ⊓ W))
    (hsup : c (subDim (V ⊔ W)) ≤ phi A (V ⊔ W)) :
    V ≤ W ∨ W ≤ V := by
  by_contra hcon
  rw [not_or] at hcon
  have hinc : ¬ (V ≤ W) ∧ ¬ (W ≤ V) := hcon
  have hslack := phi_incomparable_slack Λ V W hΛfin hA hVsat hWsat hinc
  have hmk : subDim (V ⊓ W) < subDim V :=
    subDim_inf_lt_of_ne Λ V W hVsat hWsat (fun h => hinc.1 (inf_eq_left.mp h))
  have hmℓ : subDim (V ⊓ W) < subDim W := by
    simpa [inf_comm] using subDim_inf_lt_of_ne Λ W V hWsat hVsat
      (fun h => hinc.2 (inf_eq_left.mp h))
  have hadd := subDim_inf_add_subDim_sup Λ V W hVsat hWsat
  -- the rank equation and the reverse convexity along it
  have hmn : subDim (V ⊓ W) + subDim (V ⊔ W) = subDim V + subDim W := hadd
  have hmaxn : max (subDim V) (subDim W) ≤ subDim (V ⊔ W) := by omega
  have hnd : subDim (V ⊔ W) ≤ d := subDim_le_ambient (V ⊔ W)
  have heq : subDim (V ⊓ W) + subDim (V ⊔ W) =
      min (subDim V) (subDim W) + max (subDim V) (subDim W) := by omega
  have hconv := Submission.Polygon.convex_rank_equation hcvx
    (m := subDim (V ⊓ W)) (k := min (subDim V) (subDim W))
    (ℓ := max (subDim V) (subDim W)) (n := subDim (V ⊔ W))
    (le_min hmk.le hmℓ.le) (le_trans (min_le_left _ _) (le_max_left _ _)) hmaxn hnd heq
  have hconv' : c (subDim (V ⊓ W)) + c (subDim (V ⊔ W)) ≥
      c (subDim V) + c (subDim W) := by
    have : c (min (subDim V) (subDim W)) + c (max (subDim V) (subDim W)) =
        c (subDim V) + c (subDim W) := by
      rcases le_total (subDim V) (subDim W) with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h, add_comm]
    rwa [this] at hconv
  simp only [phi] at hVtight hWtight hinf hsup hslack
  linarith [hVtight, hWtight, hinf, hsup, hconv', hslack]

/-- **Global-hypothesis form of the compatibility lemma**: if `c` is discrete-convex and
below the whole `φ_A`-data over the subgroups of `Λ`, then any two tight saturated
subgroups are comparable.  (This is the form in which the `φ_A`-Grayson polygon
`largestConvexMinorant` is consumed: it dominates no data point.) -/
theorem comparable_of_tight_of_le_data {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ}
    (hA : 0 < A) (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) {c : ℕ → ℝ}
    (hcvx : Submission.Polygon.DiscreteConvexOn c d)
    (hc : ∀ X : Submodule ℤ (E d), X ≤ Λ → c (subDim X) ≤ phi A X)
    (hVtight : phi A V = c (subDim V)) (hWtight : phi A W = c (subDim W)) :
    V ≤ W ∨ W ≤ V :=
  comparable_of_tight Λ V W hΛfin hA hVsat hWsat hcvx hVtight hWtight
    (hc _ (le_trans inf_le_left (saturated_le Λ V hVsat)))
    (hc _ (sup_le (saturated_le Λ V hVsat) (saturated_le Λ W hWsat)))

/-- **Equal-rank tight realisers coincide**: two saturated subgroups of the same rank
which are both tight for the same convex data are equal. -/
theorem eq_of_tight_of_subDim_eq {d : ℕ} (Λ V W : Submodule ℤ (E d)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d) {A : ℝ} (hA : 0 < A)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) {c : ℕ → ℝ}
    (hcvx : Submission.Polygon.DiscreteConvexOn c d)
    (hVtight : phi A V = c (subDim V)) (hWtight : phi A W = c (subDim W))
    (hinf : c (subDim (V ⊓ W)) ≤ phi A (V ⊓ W))
    (hsup : c (subDim (V ⊔ W)) ≤ phi A (V ⊔ W))
    (hdim : subDim V = subDim W) : V = W := by
  rcases comparable_of_tight Λ V W hΛfin hA hVsat hWsat hcvx hVtight hWtight hinf hsup
    with h | h
  · have hspanle : realSpan V ≤ realSpan W := Submodule.span_mono (by intro x hx; exact h hx)
    have hfin : subDim V = subDim W := hdim
    have heq : realSpan V = realSpan W :=
      Submodule.eq_of_le_of_finrank_eq hspanle (by simpa [subDim] using hfin)
    have hh : hull Λ V = hull Λ W := by
      ext x
      rw [hull_mem_iff, hull_mem_iff, heq]
    rw [hVsat, hh]
    exact hWsat.symm
  · have hspanle : realSpan W ≤ realSpan V := Submodule.span_mono (by intro x hx; exact h hx)
    have hfin : subDim W = subDim V := hdim.symm
    have heq : realSpan W = realSpan V :=
      Submodule.eq_of_le_of_finrank_eq hspanle (by simpa [subDim] using hfin)
    have hh : hull Λ W = hull Λ V := by
      ext x
      rw [hull_mem_iff, hull_mem_iff, heq]
    rw [hWsat, hh]
    exact hVsat

end Submission.PhiSlack

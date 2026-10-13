/-
# `Work.FTS.Final.ExtG.dynOK_extG` — the dynamic package of the extension `g̃ = extG g`

The physical bridge (`Work.FTS.RegPkgGal`) consumes the regularity package `RegPkgMin` of the
*extension* `g̃ = extG g` of the Galerkin family `g` to negative fake time, while the existence
argument of the strong route (`Work.FTS.StrongGlobal`, `Work.FTS.Final.DynOK`) produces it for `g`
itself.  This file transports the two clauses of `Final.DynOK`:

* `RegPkgMin α (extG g)` from `RegPkgMin α g`;
* `Xn α (slice (extG g) τ) ≤ C₀ α²` from `Xn α (slice g τ) ≤ C₀ α²` (`τ ≥ 0`).

**Why it is true.**  `extG g z θ τ = g z θ τ` whenever `z > 0` and `τ ≥ 0`, and `= 0` for
`z ≤ 0`.  Every field of the package is measured through data on the *open* half-plane `z > 0`:

* `c1` lives on `z > 0`, `τ > 0`; `c4` and `cont` on `z > 0` — pointwise congruence of `ContDiffOn`
  / `ContinuousOn`;
* `mem4` and the `Xn`-bound are statements about the weighted integrand `HkIntegrand`, which at
  `z > 0` is built from the *local* operators `DzIter`, `mixed` — so it agrees on `z > 0`
  (`HkIntegrand_congr_of_pos`, the same argument as `Work.FTS.RegPkgGal.R8`) — and *vanishes at*
  `z = 0` because of the factor `w 0 = 0` (`Work.Coercivity.HkIntegrand_zero_left`).  Since
  `Iz = [0,∞)` this pins every `z`-integral;
* `dbd` concerns `gdot g τ = ∂_τ g(·,·,τ)` for `τ > 0`: at each point the `τ`-derivative is local,
  and for `z > 0` the two families agree on a whole neighbourhood of `τ` (`extG g z θ = g z θ` for
  every `s ≥ 0`), so `gdot (extG g) τ` agrees with `gdot g τ` on `z > 0`, which by the previous
  point transfers both the `HkMem` and the `HkNorm` clause;
* `vanish` is immediate from `extG g z θ τ = 0` for `z ≤ 0` and `extG g = g` for `z > 0`, `τ ≥ 0`.

No hypothesis on the size of `α` is used beyond its presence in the statement.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Final.Defs
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.RegPkgGal.R8
import Submission.Work.Coercivity.HkMem_congr_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Filter Set MeasureTheory
open scoped Topology Real

namespace Work.FTS.Final.ExtG

set_option autoImplicit false

/-! ## Congruence of the weighted `H^k` integrand on the positive half-plane

These are the general (all `k`, all `α`) forms of the congruence argument of
`Work.FTS.RegPkgGal.R8`: the operators are local, so agreement on `z > 0` pins every integrand on
the domain `Iz = [0,∞)`, the point `z = 0` being trivial because `w 0 = 0`. -/

namespace HkAux

/-- The `H^k`-integrand of two functions that agree on the open half-plane `z > 0` agrees at every
point with `z > 0`.  (Every `DzIter`/`mixed` is a local differential operator, and the weights
only depend on `(z,θ)`.) -/
lemma HkIntegrand_congr_of_pos {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) {z θ : ℝ} (hz : 0 < z) :
    Work.Spaces.HkIntegrand α k u z θ = Work.Spaces.HkIntegrand α k v z θ := by
  have hV : IsOpen (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hagree : Set.EqOn (Function.uncurry u) (Function.uncurry v)
      (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ)) := by
    rintro ⟨z', θ'⟩ ⟨hz', -⟩
    exact h z' hz' θ'
  have hmem : (z, θ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ) := ⟨hz, trivial⟩
  simp only [Work.Spaces.HkIntegrand]
  refine congrArg₂ (· + ·) ?_ ?_
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have hh := Work.FTS.RegPkgGal.DzIter_congr_of_isOpen hV hagree i hmem
    simp only [Function.uncurry] at hh
    rw [hh]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases hij : 1 ≤ i ∧ i + j ≤ k
    · simp only [hij]
      have hh := Work.FTS.RegPkgGal.mixed_congr_of_isOpen hV hagree j i hmem
      simp only [Function.uncurry] at hh
      rw [hh]
    · simp only [hij, ite_false]

/-- The `H^k`-integrand congruence on the whole domain `Iz = [0,∞)`: the open half-plane is the
previous lemma, and at `z = 0` both integrands vanish (`w 0 = 0`). -/
lemma HkIntegrand_eq_of_mem_Iz {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    Work.Spaces.HkIntegrand α k u z θ = Work.Spaces.HkIntegrand α k v z θ := by
  have hz' : (0 : ℝ) ≤ z := hz
  rcases eq_or_lt_of_le hz' with hz0 | hzpos
  · subst hz0
    rw [Work.Coercivity.HkIntegrand_zero_left, Work.Coercivity.HkIntegrand_zero_left]
  · exact HkIntegrand_congr_of_pos h hzpos

/-- `HkSq` is insensitive to a change of the function on `z > 0`: the integrand agrees on `Iz`. -/
lemma HkSq_eq_of_Ioi {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) :
    Work.Spaces.HkSq α k u = Work.Spaces.HkSq α k v := by
  show (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k u z θ)
    = (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k v z θ)
  simp only [Work.Spaces.Iz, Work.Spaces.Iθ]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ _ => HkIntegrand_eq_of_mem_Iz h hz)

/-- `HkNorm` (and hence `Xn`) is insensitive to a change of the function on `z > 0`. -/
lemma HkNorm_eq_of_Ioi {α : ℝ} {k : ℕ} {u v : ℝ → ℝ → ℝ}
    (h : ∀ z, 0 < z → ∀ θ, u z θ = v z θ) :
    Work.Spaces.HkNorm α k u = Work.Spaces.HkNorm α k v := by
  simp only [Work.Spaces.HkNorm]
  rw [HkSq_eq_of_Ioi h]

end HkAux

/-! ## The pointwise coincidences for the extension `g̃ = extG g` -/

/-- On `z > 0` and `τ ≥ 0` the extension is the family itself. -/
lemma slice_extG_eq_of_pos {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 ≤ τ) (hz : 0 < z) :
    Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.FTS.Galerkin.slice g τ z θ := by
  simp only [Work.FTS.Galerkin.slice]
  exact Work.FTS.RegPkgGal.extG_of_pos hz hτ

/-- The `ℋ⁴`-size of the extended slice equals that of the original slice, for `τ ≥ 0`. -/
lemma Xn_extG_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ} (hτ : 0 ≤ τ) :
    Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ)
      = Work.FTS.Nonlin.Xn α (Work.FTS.Galerkin.slice g τ) :=
  HkAux.HkNorm_eq_of_Ioi (k := 4) (fun _z hz _ => slice_extG_eq_of_pos hτ hz)

/-- The `ℋ^k`-membership of the extended slice, for `τ ≥ 0`. -/
lemma mem_slice_extG {α : ℝ} {k : ℕ} {g : Work.FTS.Galerkin.Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (h : Work.Spaces.HkMem α k (Work.FTS.Galerkin.slice g τ)) :
    Work.Spaces.HkMem α k (Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ) :=
  Work.Coercivity.HkMem_congr_Ioi α k h
    (fun _z hz _ _ => (slice_extG_eq_of_pos hτ hz).symm)

/-- The fake-time derivative of the extension is that of the family on `z > 0`, for `τ > 0`
(the `τ`-derivative is local, and for `z > 0` the two functions agree on a neighbourhood of `τ`). -/
lemma gdot_extG_eq_of_pos {g : Work.FTS.Galerkin.Fam} {τ z θ : ℝ} (hτ : 0 < τ) (hz : 0 < z) :
    Work.FTS.Galerkin.gdot (Work.FTS.RegPkgGal.extG g) τ z θ
      = Work.FTS.Galerkin.gdot g τ z θ := by
  have hev : (fun s => Work.FTS.RegPkgGal.extG g z θ s) =ᶠ[𝓝 τ] (fun s => g z θ s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hτ] with s hs
    exact Work.FTS.RegPkgGal.extG_of_pos hz (le_of_lt hs)
  simpa only [Work.FTS.Galerkin.gdot] using hev.deriv_eq

/-! ## The four structural fields of `RegPkgMin` -/

/-- The horizon-local `ℋ³`-bound on `∂_τ g` transfers to the extension. -/
lemma dbd_extG {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (h : ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot g τ)
      ∧ Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot g τ) ≤ Cd) :
    ∀ S, 0 < S → ∃ Cd, ∀ τ, 0 < τ → τ < S →
      Work.Spaces.HkMem α 3 (Work.FTS.Galerkin.gdot (Work.FTS.RegPkgGal.extG g) τ)
      ∧ Work.Spaces.HkNorm α 3 (Work.FTS.Galerkin.gdot (Work.FTS.RegPkgGal.extG g) τ) ≤ Cd := by
  intro S hS
  obtain ⟨Cd, hCd⟩ := h S hS
  refine ⟨Cd, fun τ hτ hτS => ⟨?_, ?_⟩⟩
  · exact Work.Coercivity.HkMem_congr_Ioi α 3 (hCd τ hτ hτS).1
      (fun z hz _ _ => (gdot_extG_eq_of_pos hτ hz).symm)
  · rw [HkAux.HkNorm_eq_of_Ioi (k := 3) (fun z hz _ => gdot_extG_eq_of_pos hτ hz)]
    exact (hCd τ hτ hτS).2

/-- Vanishing on the two angular boundaries transfers to the extension. -/
lemma vanish_extG {g : Work.FTS.Galerkin.Fam}
    (h : ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z → g z 0 τ = 0 ∧ g z (π / 2) τ = 0) :
    ∀ τ, 0 ≤ τ → ∀ z, 0 ≤ z →
      Work.FTS.RegPkgGal.extG g z 0 τ = 0 ∧ Work.FTS.RegPkgGal.extG g z (π / 2) τ = 0 := by
  intro τ hτ z hz
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    exact ⟨Work.FTS.RegPkgGal.extG_of_nonpos le_rfl,
      Work.FTS.RegPkgGal.extG_of_nonpos le_rfl⟩
  · obtain ⟨h1, h2⟩ := h τ hτ z (le_of_lt hzpos)
    exact ⟨by rw [Work.FTS.RegPkgGal.extG_of_pos hzpos hτ, h1],
      by rw [Work.FTS.RegPkgGal.extG_of_pos hzpos hτ, h2]⟩

/-- Joint interior `C¹`-regularity transfers to the extension (the slab has `z > 0`, `τ > 0`,
where the extension agrees with the family). -/
lemma c1_extG {g : Work.FTS.Galerkin.Fam}
    (h : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0)) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FTS.RegPkgGal.extG g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi 0) :=
  h.congr (fun _p hp => Work.FTS.RegPkgGal.extG_of_pos hp.1 (le_of_lt hp.2.2))

/-- Spatial `C⁴`-regularity of the slices transfers to the extension (the quadrant `Q0` has
`z > 0`). -/
lemma c4_extG {g : Work.FTS.Galerkin.Fam}
    (h : ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0) :
    ∀ τ, 0 ≤ τ → ContDiffOn ℝ 4
      (Function.uncurry (Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ))
      Work.FTS.EllipticEst.Q0 := by
  intro τ hτ
  refine (h τ hτ).congr (fun p hp => ?_)
  show Work.FTS.Galerkin.slice (Work.FTS.RegPkgGal.extG g) τ p.1 p.2
    = Work.FTS.Galerkin.slice g τ p.1 p.2
  exact slice_extG_eq_of_pos hτ hp.1

/-- Continuity in fake time up to `τ = 0` at the points of the open quadrant transfers to the
extension. -/
lemma cont_extG {g : Work.FTS.Galerkin.Fam}
    (h : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => g z θ τ) (Set.Ici 0)) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => Work.FTS.RegPkgGal.extG g z θ τ) (Set.Ici 0) := by
  intro z θ hz
  refine (h z θ hz).congr (fun τ hτ => ?_)
  exact Work.FTS.RegPkgGal.extG_of_pos hz.1 hτ

/-! ## The transport of `DynOK` -/

theorem dynOK_extG {α C₀ : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fam}
    (h : Work.FTS.Final.DynOK α C₀ g) :
    Work.FTS.Final.DynOK α C₀ (Work.FTS.RegPkgGal.extG g) := by
  have hα0 : (0 : ℝ) < α := hα
  obtain ⟨hmin, hbd⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact c1_extG hmin.c1
  · exact c4_extG hmin.c4
  · exact cont_extG hmin.cont
  · intro τ hτ; exact mem_slice_extG hτ (hmin.mem4 τ hτ)
  · exact dbd_extG hmin.dbd
  · exact vanish_extG hmin.vanish
  · intro τ hτ
    rw [Xn_extG_eq hτ]
    exact hbd τ hτ

end Work.FTS.Final.ExtG

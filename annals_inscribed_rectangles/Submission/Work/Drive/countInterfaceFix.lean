import Mathlib
import Submission.Work.Drive.parityCore_of_functional

/-!
# The count interface of the chain route: the global-continuity defect and its repair

The chain route produces `ParityCore γ` from a two-variable count
`n u v = #(C₀ ⋔ A_u v) (mod 2)` (the mod-2 intersection number of the cut `A_u v = P_u ∩ V_v` with the
essential loop `C₀` of `P₀`).  The bridging theorems of the workspace
(`Work.Drive.stripRel_of_count`, `Work.Drive.parityCore_of_count`,
`Submission/Work/Drive/parityCore_of_functional.lean`) list the four properties the count has to
satisfy; the fourth of them, `hn4`, asks for

> `Continuous (fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2)`,

i.e. for the **global** continuity of the count on the whole rotation torus.  This file records that
this hypothesis is unsatisfiable as soon as `Zc γ ≠ ∅`:

* a continuous `ZMod 2`-valued function on the rotation torus is **constant** (`ZMod 2` is discrete and
  the torus is connected);
* combined with the rotation invariance `hn1 : n u v = n 0 (v - u)` it makes the count a function
  `φ (v - u)` of the difference only;
* combined with the antisymmetry `hn2` on pairs with `v - u ∈ Zc γ` it forces `2 · φ 0 = 1` in
  `ZMod 2`, which is impossible — but only if `Zc γ` is nonempty.

Hence `hn1 ∧ hn2 ∧ hn4` holds **iff** `Zc γ = ∅`, in which case `ParityCore γ` is trivially true
(and, conversely, `ParityCore γ` is trivial exactly then): the two bridging theorems are *vacuous*
(theorem `exists_count_iff_Zc_eq_empty` below, and `parityCore_of_Zc_eq_empty`).

The repair is forced and is a one-line weakening: the count is only ever used at pairs with
`n u v = 1`, and the openness clause of `Work.Drive.StripRel` needs local constancy *there* only.  The
corrected hypothesis is

> `∀ u v, n u v = 1 → ∀ᶠ p in 𝓝 (u, v), n p.1 p.2 = 1`,

i.e. the count is locally constant at the pairs where it is `1` — which is exactly what the geometric
count satisfies (the chains are transverse there) and what fails at the diagonal `u = v`, where the two
planes collide.  `stripRel_of_count_local` and `parityCore_of_count_local` below are the corrected
bridges, with the same proofs as the originals.

## Why the geometric count cannot be globally continuous

For `v - u ∈ Zc γ` the cut `A_u v` is a closed `1`-cycle of `P_u` disjoint from `C₀ ⊂ P_u` (the planes
`P_u`, `P_v` are disjoint), so the count is locally constant as a function of the pair.  As
`v - u → 0 ∈ GoodC γ` the planes cross, `A_u v` sweeps over all of `P_u`, and the count jumps; the
discontinuity of `φ` at the boundary of `Zc γ` is exactly the phenomenon that `one_half_mem_GoodC`
freezes at `u = 1/2`.  There is no global continuous representative, hence the interface of the route
must be stated on `Zc γ` (as `Work.Drive.parityCore_of_functional` does: `e : Zc γ → ZMod 2`).
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

/-- A `ZMod 2`-valued function which is constant, in the form used below. -/
private lemma zmod2_add_self' (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

/-- **Any continuous `ZMod 2`-valued function on the rotation torus is constant.**  `ZMod 2` carries the
discrete topology and the torus is connected. -/
lemma eq_of_continuous_zmod2 {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → ZMod 2) (hf : Continuous f) (p q : X) : f p = f q :=
  ((IsLocallyConstant.iff_continuous f).mpr hf).apply_eq_of_preconnectedSpace p q

/-- **The global-continuity defect.**  A count satisfying the rotation invariance `hn1`, the
antisymmetry `hn2` on disjoint pairs and the global continuity `hn4` can exist only if `Zc γ` is
empty. -/
theorem Zc_eq_empty_of_continuousCount {γ : Circle → ℝ × ℝ}
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn4 : Continuous fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2) :
    Zc γ = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.mpr fun u hu => ?_
  have hφ : Continuous fun t : UnitAddCircle => n 0 t :=
    hn4.comp (continuous_const.prodMk continuous_id)
  have hconst : ∀ t : UnitAddCircle, n 0 t = n 0 0 := fun t =>
    eq_of_continuous_zmod2 _ hφ t 0
  have h := hn2 0 u (by simpa using hu)
  rw [hn1 u 0, hconst u, hconst (0 - u)] at h
  have hz := zmod2_add_self' (n 0 0)
  rw [hz] at h
  exact zero_ne_one h

/-- **The global-count interface is satisfiable only in the trivial case.**  There is a count with the
three properties listed above if and only if the collision set of `γ` is everything. -/
theorem exists_count_iff_Zc_eq_empty {γ : Circle → ℝ × ℝ} :
    (∃ n : UnitAddCircle → UnitAddCircle → ZMod 2,
      (∀ u v : UnitAddCircle, n u v = n 0 (v - u)) ∧
      (∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1) ∧
      Continuous fun p : UnitAddCircle × UnitAddCircle => n p.1 p.2) ↔ Zc γ = ∅ := by
  constructor
  · rintro ⟨n, h1, h2, h4⟩
    exact Zc_eq_empty_of_continuousCount n h1 h2 h4
  · intro h
    exact ⟨fun _ _ => 0, fun _ _ => rfl, fun u v hv => by rw [h] at hv; exact absurd hv (Set.notMem_empty u),
      continuous_const⟩

/-- **`Zc γ` is empty exactly when the collision set of `γ` is everything.**  Since the aspect ratio
of the inscribed rectangle attached to a collision angle `u = e^{iθ}` is `tan (θ/4)` and `u`, `u⁻¹` give
the same aspect ratio (proof of Theorem 1 of `_ref/OneThird.tex`), this is the statement that *every*
aspect ratio occurs — the conjecture quoted in the paper's introduction as long-standing, and which the
paper's Theorem 4 shows to be false for general Möbius strips filling `T(2,1)`. -/
theorem Zc_eq_empty_iff_goodC_eq_univ (γ : Circle → ℝ × ℝ) :
    Zc γ = ∅ ↔ Submission.Configuration.GoodC γ = Set.univ := by
  rw [Zc_eq_compl]
  constructor
  · intro h
    exact Set.eq_univ_iff_forall.mpr fun x => by
      by_contra hx
      exact Set.eq_empty_iff_forall_notMem.mp h x (by simpa using hx)
  · intro h
    rw [h, Set.compl_univ]

/-- **`ParityCore γ` is trivial when `Zc γ` is empty** — every clause quantifies over `Zc γ` only.  (This
is the hypothesis under which `parityCore_of_count` is usable; when `Zc γ ≠ ∅` its hypotheses are
contradictory.) -/
theorem parityCore_of_Zc_eq_empty {γ : Circle → ℝ × ℝ} (h : Zc γ = ∅) : ParityCore γ := by
  refine ⟨fun _ => 0, continuous_const, ?_, ?_⟩
  · intro u hu
    rw [h] at hu
    exact absurd hu (Set.notMem_empty u)
  · intro a ha
    rw [h] at ha
    exact absurd ha (Set.notMem_empty a)

/-- **The corrected bridge.**  `StripRel γ Rel` from a two-variable count, with the global continuity
of `Work.Drive.stripRel_of_count`'s `hn4` replaced by the local constancy *at the pairs where the count
is `1`* — the only thing the openness clause needs, and exactly what the geometric count satisfies.

Clauses 1–3 are as in `Work.Drive.stripRel_of_count`; clause 4 uses `hn4` at `(u, v)` with `n u v = 1`
and `mem_nhds_prod_iff'`. -/
theorem stripRel_of_count_local {γ : Circle → ℝ × ℝ}
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn3 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1)
    (hn4 : ∀ u v : UnitAddCircle, n u v = 1 →
      ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 (u, v), n p.1 p.2 = 1) :
    ∃ Rel : UnitAddCircle → UnitAddCircle → Prop, StripRel γ Rel := by
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  refine ⟨fun u v => n u v = 1, ?_, ?_, ?_, ?_⟩
  · -- clause 1: antisymmetry
    intro u v hv
    constructor
    · intro huv hvu
      have h := hn2 u v hv
      rw [huv] at h
      have h0 : n v u = 0 := (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
      rw [h0] at hvu
      exact zero_ne_one hvu
    · intro hvu
      have h := hn2 u v hv
      rcases hcases (n v u) with h0 | h1
      · simpa [h0] using h
      · exact absurd h1 hvu
  · -- clause 2: rotation invariance
    intro u v w
    show (n u v = 1) ↔ (n (u + w) (v + w) = 1)
    have hsub : (v + w) - (u + w) = v - u := by abel
    rw [hn1 (u + w) (v + w), hn1 u v, hsub]
  · -- clause 3: transitivity
    intro u v w huv hvw huw huvW hvwW
    set a : UnitAddCircle := v - u with ha_def
    set c : UnitAddCircle := w - v with hc_def
    have ha : a ∈ Zc γ := huv
    have hc : c ∈ Zc γ := hvw
    have hsum : a + c = w - u := by rw [ha_def, hc_def]; abel
    have hac : a + c ∈ Zc γ := by rw [hsum]; exact huw
    have hea : n 0 a = 1 := by rw [← hn1 u v]; exact huvW
    have hec : n 0 c = 1 := by rw [← hn1 v w]; exact hvwW
    have ha' : a - 0 ∈ Zc γ := by simpa using ha
    have hna : n 0 (-a) = 0 := by
      have h := hn2 0 a ha'
      have h1 : n a 0 = n 0 (-a) := by simpa using hn1 a 0
      rw [h1, hea] at h
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
    have hc' : c - 0 ∈ Zc γ := by simpa using hc
    have hnc : n 0 (-c) = 0 := by
      have h := hn2 0 c hc'
      have h1 : n c 0 = n 0 (-c) := by simpa using hn1 c 0
      rw [h1, hec] at h
      exact (add_left_inj (1 : ZMod 2)).mp (by simpa using h)
    have h3 := hn3 a ha c hc hac
    have hkey : n 0 (a + c) = 1 := by
      rw [hea, hna, hec, hnc] at h3
      simpa using h3
    show n u w = 1
    rw [hn1 u w]
    rwa [← hsum]
  · -- clause 4: openness, from local constancy at the pairs with count `1`
    intro u v _ huvW
    obtain ⟨U, V, hUo, huU, hVo, hvV, hUV⟩ :=
      mem_nhds_prod_iff'.mp (hn4 u v huvW)
    exact ⟨U, V, hUo, hVo, huU, hvV, fun u' hu' v' hv' _ => by
      simpa using hUV (Set.mk_mem_prod hu' hv')⟩

/-- **The clean form of the corrected interface: the count restricted to `Zc γ`.**

The geometric count is only meaningful at pairs with `v - u ∈ Zc γ`, and it is *there* (not globally)
that it is locally constant.  This theorem takes `hn4` to say exactly that: the side function
`u ↦ n 0 u` is locally constant on `Zc γ` (`∀ᶠ` in the subspace topology).  The conclusion is
`ParityCore γ` through the sharp interface `Work.Drive.parityCore_of_functional`; no global continuity of
`(u, v) ↦ n u v` is asked for, and none exists (see `Zc_eq_empty_of_continuousCount`).

The hypotheses `hn1`–`hn3` are those of `Work.Drive.stripRel_of_count` / `parityCore_of_count`; `hn2`
uses only the pairs with `u - 0 ∈ Zc γ`. -/
theorem parityCore_of_countOnZc {γ : Circle → ℝ × ℝ}
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn3 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1)
    (hn4 : ∀ x : Zc γ, ∀ᶠ y : Zc γ in 𝓝 x, n 0 (y : UnitAddCircle) = n 0 (x : UnitAddCircle)) :
    ParityCore γ := by
  have hloc : IsLocallyConstant (fun x : Zc γ => n 0 (x : UnitAddCircle)) :=
    (IsLocallyConstant.iff_eventually_eq _).mpr hn4
  refine parityCore_of_functional _ hloc.continuous ?_ ?_
  · intro u hu
    have h := hn2 0 u (by simpa using hu)
    have h' : n u 0 = n 0 (-u) := by simpa using hn1 u 0
    show n 0 u + n 0 (-u) = 1
    rw [← h']
    exact h
  · intro a ha c hc hac
    exact hn3 a ha c hc hac

/-- **`ParityCore γ` from the corrected count interface** — `stripRel_of_count_local` composed with
`Work.Drive.parityCore_of_stripRel`.  This is the usable form of `Work.Drive.parityCore_of_count`. -/
theorem parityCore_of_count_local {γ : Circle → ℝ × ℝ}
    (n : UnitAddCircle → UnitAddCircle → ZMod 2)
    (hn1 : ∀ u v : UnitAddCircle, n u v = n 0 (v - u))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ → n u v + n v u = 1)
    (hn3 : ∀ (a : UnitAddCircle) (ha : a ∈ Zc γ) (c : UnitAddCircle) (hc : c ∈ Zc γ)
      (hac : a + c ∈ Zc γ),
      n 0 a * n 0 (a + c) + n 0 (-a) * n 0 c + n 0 (-(a + c)) * n 0 (-c) = 1)
    (hn4 : ∀ u v : UnitAddCircle, n u v = 1 →
      ∀ᶠ p : UnitAddCircle × UnitAddCircle in 𝓝 (u, v), n p.1 p.2 = 1) :
    ParityCore γ :=
  (stripRel_of_count_local n hn1 hn2 hn3 hn4).elim (fun _ hRel => parityCore_of_stripRel hRel)

end Work.Drive

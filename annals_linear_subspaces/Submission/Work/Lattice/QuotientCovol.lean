import Mathlib
import Submission.Work.Lattice.WedgeProjection
import Submission.Work.Lattice.AlignedBases

/-!
# The projected-quotient covolume factorisation (P2 block layer, step A3)

For a nested pair `V ≤ W` of subgroups of a full-rank lattice `Λ ≤ ℝᵈ`, the block analysis
of §3 controls the **quotient** `W/V` — realised as the orthogonal projection
`Q := π(W) ⊆ (realSpan V)ᗮ` with `π := starProjection (realSpan V)ᗮ`.  This module proves
the exact **factorisation of the covolume**:

    `latticeCovol W = latticeCovol V · latticeCovol Q`.

The proof is the exterior-algebra route recorded in the ROADMAP: take an aligned family
`u : Fin m → ℝᵈ` spanning `V` and `y : Fin b → ℝᵈ` completing it to `W` (both `ℝ`-independent,
`AlignedBases.exists_aligned_ambient_of_saturated_pair`); then

* `ιMulti (u ++ y) = ιMulti (u ++ π ∘ y)`: the correction `y j − π y j` lies in
  `realSpan V = span ℝ (range u)`, and an alternating multilinear form is unchanged by
  slotwise corrections lying in the span of the *other* entries
  (`iMulti_add_correction_eq_self`, proved by a `Finset` induction using
  `AlternatingMap.map_update_add` + `AlternatingMap.map_linearDependent`);
* `‖ιMulti (u ++ π ∘ y)‖ = ‖ιMulti u‖ · ‖ιMulti (π ∘ y)‖` by the orthogonal-concatenation
  identity (Commons `exteriorPower_norm_concat_orthogonal`);
* `latticeCovol` of a `ℤ`-span of an `ℝ`-independent family is its wedge norm
  (`latticeCovol_span`).

The identity is the exact statement that "the covolume is multiplicative in the quotient",
the missing lattice-theoretic input of the per-block `log μᵢ = slope + O(1)` analysis
(combined with Minkowski-2-upper on `Q` and the "no short vector" bound
`QuotientShort.log_dist_ge_polygon_slope`).

All declarations are Mathlib + Submission (WedgeProjection, AlignedBases).
-/

noncomputable section
open Set Module Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1200000

namespace Submission.QuotientCovol

open Submission.GraysonData
open Submission.GraysonLattice
open Submission.JoinSubmodularity
open Submission.AlignedBases
open Submission.IntrinsicIndex

/-! ## 1. The slot-correction lemmas for `ιMulti` -/

/-- **Slot replacement by a vector in the span of the other entries.**  For a family
`f : Fin n → E` and an index `i`, replacing the `i`-th entry by a vector lying in the span
of the remaining entries kills the exterior product. -/
lemma iMulti_update_eq_zero_of_mem_span {d n : ℕ} (f : Fin n → E d) (i : Fin n) (c : E d)
    (hc : c ∈ Submodule.span ℝ (Set.range (fun j : {j : Fin n // j ≠ i} => f j))) :
    exteriorPower.ιMulti ℝ n (Function.update f i c) = 0 := by
  refine AlternatingMap.map_linearDependent (exteriorPower.ιMulti ℝ n) _ ?_
  intro hLI
  apply hLI.notMem_span i
  have himg : (Function.update f i c) '' {i}ᶜ =
      Set.range (fun j : {j : Fin n // j ≠ i} => f j) := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      have hji : j ≠ i := by simpa using hj
      exact ⟨⟨j, hji⟩, by rw [Function.update_of_ne hji]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, by simpa using j.2, by rw [Function.update_of_ne j.2]⟩
  rw [himg, Function.update_self]
  exact hc

/-- **Iterated slot corrections.**  If `δ` vanishes outside a finite set `J` of indices and
on `J` takes values in the span of the `f`-values at the *complementary* indices, then
`ιMulti (f + δ) = ιMulti f`. -/
lemma iMulti_add_correction_eq_self {d n : ℕ} (f δ : Fin n → E d) (J : Finset (Fin n))
    (h0 : ∀ i ∉ J, δ i = 0)
    (h : ∀ i ∈ J, δ i ∈ Submodule.span ℝ (Set.range (fun j : {j : Fin n // j ∉ J} => f j))) :
    exteriorPower.ιMulti ℝ n (fun i => f i + δ i) = exteriorPower.ιMulti ℝ n f := by
  classical
  let F : Finset (Fin n) → (Fin n → E d) := fun s i => if i ∈ s then f i + δ i else f i
  have key : ∀ s : Finset (Fin n), s ⊆ J →
      exteriorPower.ιMulti ℝ n (F s) = exteriorPower.ιMulti ℝ n (F ∅) := by
    intro s
    refine Finset.induction (motive := fun t : Finset (Fin n) => t ⊆ J →
        exteriorPower.ιMulti ℝ n (F t) = exteriorPower.ιMulti ℝ n (F ∅)) ?_ ?_ s
    · intro _
      rfl
    · intro a s ha ih hsJ
      have haJ : a ∈ J := hsJ (Finset.mem_insert_self a s)
      have hsJ' : s ⊆ J := fun x hx => hsJ (Finset.mem_insert_of_mem hx)
      have hst : F (insert a s) = Function.update (F s) a (f a + δ a) := by
        funext i
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self]
          simp [F]
        · rw [Function.update_of_ne hi]
          simp only [F, Finset.mem_insert, hi, false_or]
      rw [hst]
      have hstep := AlternatingMap.map_update_add (exteriorPower.ιMulti ℝ n) (F s) a
        (f a) (δ a)
      rw [hstep]
      have hself : Function.update (F s) a (f a) = F s := by
        funext i
        by_cases hi : i = a
        · subst hi
          rw [Function.update_self]
          simp [F, ha]
        · rw [Function.update_of_ne hi]
      have hz : exteriorPower.ιMulti ℝ n (Function.update (F s) a (δ a)) = 0 := by
        refine iMulti_update_eq_zero_of_mem_span (F s) a (δ a) ?_
        refine Submodule.span_mono ?_ (h a haJ)
        rintro x ⟨j, rfl⟩
        have hjs : j.1 ∉ s := fun hs => j.2 (hsJ' hs)
        refine ⟨⟨j.1, fun hja => j.2 (hja ▸ haJ)⟩, ?_⟩
        simp only [F]
        rw [if_neg hjs]
      rw [hself, hz, add_zero]
      exact ih hsJ'
  have hFJ : F J = fun i => f i + δ i := by
    funext i
    by_cases hi : i ∈ J
    · simp [F, hi]
    · simp [F, hi, h0 i hi]
  have hF0 : F ∅ = f := by
    funext i
    simp [F]
  rw [← hFJ, ← hF0]
  exact key J (subset_refl J)

/-- **Correction of the tail of an appended family.**  If every tail vector `x j` differs
from `πx j` by a vector in the span of the head family `u`, then the exterior product of
`u ++ x` equals that of `u ++ πx`. -/
lemma iMulti_append_sub_mem_span {d m a : ℕ} (u : Fin m → E d) (x πx : Fin a → E d)
    (h : ∀ j, x j - πx j ∈ Submodule.span ℝ (Set.range u)) :
    exteriorPower.ιMulti ℝ (m + a) (Fin.append u x) =
      exteriorPower.ιMulti ℝ (m + a) (Fin.append u πx) := by
  classical
  have hfam : (fun i : Fin (m + a) =>
      Fin.append u x i + (Fin.append u πx i - Fin.append u x i)) = Fin.append u πx := by
    funext i
    abel
  rw [← hfam]
  set J : Finset (Fin (m + a)) := Finset.univ.filter (fun i => m ≤ i.val) with hJ
  have hmemJ : ∀ i : Fin (m + a), i ∈ J ↔ m ≤ i.val := by
    intro i
    simp [hJ]
  have hnotJ : ∀ i : Fin (m + a), i ∉ J ↔ i.val < m := by
    intro i
    rw [hmemJ i]
    omega
  have hrange : Set.range (fun j : {j : Fin (m + a) // j ∉ J} => Fin.append u x j)
      = Set.range u := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      have hlt : j.1.val < m := (hnotJ j.1).mp j.2
      have hcast : j.1 = Fin.castAdd a ⟨j.1.val, hlt⟩ := Fin.ext rfl
      refine ⟨⟨j.1.val, hlt⟩, ?_⟩
      have h1 : Fin.append u x (Fin.castAdd a ⟨j.1.val, hlt⟩) = u ⟨j.1.val, hlt⟩ :=
        Fin.append_left u x _
      exact h1.symm.trans (congrArg (Fin.append u x) hcast)
    · rintro ⟨i, rfl⟩
      have hlt : (Fin.castAdd a i).val < m := i.isLt
      exact ⟨⟨Fin.castAdd a i, (hnotJ _).mpr hlt⟩, Fin.append_left u x i⟩
  refine (iMulti_add_correction_eq_self (Fin.append u x)
    (fun i => Fin.append u πx i - Fin.append u x i) J ?_ ?_).symm
  · intro i hi
    have hlt : i.val < m := (hnotJ i).mp hi
    have hcast : i = Fin.castAdd a ⟨i.val, hlt⟩ := Fin.ext rfl
    rw [hcast, Fin.append_left, Fin.append_left, sub_self]
  · intro i hi
    have hge : m ≤ i.val := (hmemJ i).mp hi
    have hjn : i.val - m < a := by have := i.isLt; omega
    have hcast : i = Fin.natAdd m ⟨i.val - m, hjn⟩ := Fin.ext (Nat.add_sub_cancel' hge).symm
    rw [hcast, Fin.append_right, Fin.append_right, hrange]
    simpa only [neg_sub] using Submodule.neg_mem _ (h ⟨i.val - m, hjn⟩)

/-! ## 2. The projection identity -/

/-- **The exterior product is unchanged by orthogonal projection of the tail.**  For an
`ℝ`-independent head family `u` and any tail `y`, with `π := starProjection (span ℝ (range u))ᗮ`,
the wedge of `u ++ y` equals the wedge of `u ++ π ∘ y`. -/
lemma iMulti_append_starProjection {d m b : ℕ} (u : Fin m → E d) (y : Fin b → E d) :
    exteriorPower.ιMulti ℝ (m + b) (Fin.append u y) =
      exteriorPower.ιMulti ℝ (m + b)
        (Fin.append u (fun j => (Submodule.span ℝ (Set.range u))ᗮ.starProjection (y j))) := by
  classical
  set V₀ : Submodule ℝ (E d) := Submodule.span ℝ (Set.range u) with hV₀
  refine iMulti_append_sub_mem_span u y (fun j => V₀ᗮ.starProjection (y j)) ?_
  intro j
  have h1 : y j - V₀ᗮ.starProjection (y j) ∈ (V₀ᗮ)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (y j)
  rw [Submodule.orthogonal_orthogonal] at h1
  simp only [hV₀] at h1
  exact h1

/-- **Linear independence of the projected tail.**  If the head family `u` and the
concatenation `u ++ y` are `ℝ`-independent, then the projected tail
`π ∘ y` (`π := starProjection (span ℝ (range u))ᗮ`) is `ℝ`-independent. -/
lemma linearIndependent_starProjection {d m b : ℕ} (u : Fin m → E d) (y : Fin b → E d)
    (huy : LinearIndependent ℝ (Fin.append u y)) :
    LinearIndependent ℝ (fun j => (Submodule.span ℝ (Set.range u))ᗮ.starProjection (y j)) := by
  classical
  set V₀ : Submodule ℝ (E d) := Submodule.span ℝ (Set.range u) with hV₀
  set pr : E d →L[ℝ] E d := V₀ᗮ.starProjection with hpr
  have hyker : ∀ c : Fin b → ℝ, (∑ j, c j • pr (y j)) = 0 → ∀ j, c j = 0 := by
    intro c hc
    -- the combination of `y`'s lies in `V₀`
    have hmem : (∑ j, c j • y j) ∈ Submodule.span ℝ (Set.range u) := by
      have h0 : pr (∑ j, c j • y j) = 0 := by
        rw [map_sum]
        simpa only [ContinuousLinearMap.map_smul] using hc
      have h1 : (∑ j, c j • y j) ∈ (V₀ᗮ)ᗮ :=
        (Submodule.starProjection_apply_eq_zero_iff (V₀ᗮ)).mp h0
      rw [Submodule.orthogonal_orthogonal] at h1
      simpa [hV₀] using h1
    -- a relation on the appended family
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (R := ℝ)
      (v := u)).mp hmem
    have hg : (∑ i : Fin (m + b), (Fin.append a (fun j => -c j)) i •
        (Fin.append u y) i) = 0 := by
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right, neg_smul, Finset.sum_neg_distrib]
      rw [ha]
      abel
    have hg0 := (Fintype.linearIndependent_iff.mp huy) (Fin.append a (fun j => -c j)) hg
    intro j
    have hj : -c j = 0 := by simpa using hg0 (Fin.natAdd m j)
    exact neg_eq_zero.mp hj
  exact Fintype.linearIndependent_iff.mpr hyker

/-- **The projected-quotient covolume factorisation (family form).**  Let `u : Fin m → ℝᵈ`
(`0 < m`) and `y : Fin b → ℝᵈ` be such that `u` and `u ++ y` are `ℝ`-independent.  Then

`latticeCovol (span ℤ (range (u ++ y))) =
   latticeCovol (span ℤ (range u)) · ‖ιMulti (π ∘ y)‖`,

`π := starProjection (span ℝ (range u))ᗮ` — i.e. forming the `ℤ`-span of the projected tail
multiplies the covolume exactly by the covolume of the quotient. -/
theorem latticeCovol_append_eq_mul_norm_iMulti_starProjection {d m b : ℕ} (hm : 0 < m)
    (u : Fin m → E d) (y : Fin b → E d)
    (hu : LinearIndependent ℝ u) (huy : LinearIndependent ℝ (Fin.append u y)) :
    latticeCovol (Submodule.span ℤ (Set.range (Fin.append u y))) =
      latticeCovol (Submodule.span ℤ (Set.range u)) *
        ‖exteriorPower.ιMulti ℝ b
          (fun j => (Submodule.span ℝ (Set.range u))ᗮ.starProjection (y j))‖ := by
  classical
  set V₀ : Submodule ℝ (E d) := Submodule.span ℝ (Set.range u) with hV₀
  set pr : E d →L[ℝ] E d := V₀ᗮ.starProjection with hpr
  set x : Fin b → E d := fun j => pr (y j) with hx
  have horth : ∀ i : Fin m, ∀ j : Fin b, inner ℝ (u i) (x j) = 0 := by
    intro i j
    have hmem : x j ∈ V₀ᗮ := by
      rw [hx]
      exact Submodule.starProjection_apply_mem _ (y j)
    have h := (Submodule.mem_orthogonal' V₀ (x j)).mp hmem (u i)
      (by rw [hV₀]; exact Submodule.subset_span ⟨i, rfl⟩)
    rwa [real_inner_comm] at h
  have hnorm : ‖exteriorPower.ιMulti ℝ (m + b) (Fin.append u y)‖ =
      ‖exteriorPower.ιMulti ℝ m u‖ * ‖exteriorPower.ιMulti ℝ b x‖ := by
    rw [iMulti_append_starProjection u y, hx, hpr,
      Commons.Analysis.InnerProductSpace.exteriorPower_norm_concat_orthogonal u x horth]
  have hcovW : latticeCovol (Submodule.span ℤ (Set.range (Fin.append u y))) =
      ‖exteriorPower.ιMulti ℝ (m + b) (Fin.append u y)‖ :=
    latticeCovol_span (by omega) _ huy
  have hcovV : latticeCovol (Submodule.span ℤ (Set.range u)) =
      ‖exteriorPower.ιMulti ℝ m u‖ := latticeCovol_span hm _ hu
  rw [hcovW, hcovV, hnorm]

/-! ## 3. Covolume form of the projection identity -/

/-- **The projected-quotient covolume factorisation (covolume form).**  Family form with
the covolume of the projected tail lattice on the right: for `ℝ`-independent `u` (`0 < m`)
and `u ++ y`, and `0 < b`,

`latticeCovol (span ℤ (range (u ++ y))) =
   latticeCovol (span ℤ (range u)) · latticeCovol (span ℤ (range (π ∘ y)))`,

`π := starProjection (span ℝ (range u))ᗮ`. -/
theorem latticeCovol_append_eq_mul_latticeCovol_starProjection {d m b : ℕ} (hm : 0 < m)
    (hb : 0 < b) (u : Fin m → E d) (y : Fin b → E d)
    (hu : LinearIndependent ℝ u) (huy : LinearIndependent ℝ (Fin.append u y)) :
    latticeCovol (Submodule.span ℤ (Set.range (Fin.append u y))) =
      latticeCovol (Submodule.span ℤ (Set.range u)) *
        latticeCovol (Submodule.span ℤ (Set.range
          (fun j => (Submodule.span ℝ (Set.range u))ᗮ.starProjection (y j)))) := by
  rw [latticeCovol_append_eq_mul_norm_iMulti_starProjection hm u y hu huy,
    latticeCovol_span hb _ (linearIndependent_starProjection u y huy)]

/-! ## 4. The saturated-pair version -/

/-- The `ℤ`-linear orthogonal projection onto `(realSpan V)ᗮ`. -/
def projMap {d : ℕ} (V : Submodule ℤ (E d)) : E d →ₗ[ℤ] E d :=
  (((realSpan V)ᗮ.starProjection : E d →L[ℝ] E d).toLinearMap).restrictScalars ℤ

/-- Evaluation of `projMap`. -/
@[simp] lemma projMap_apply {d : ℕ} (V : Submodule ℤ (E d)) (x : E d) :
    projMap V x = (realSpan V)ᗮ.starProjection x := rfl

/-- A vector of a subspace `U` is killed by the projection onto its orthogonal complement. -/
lemma starProjection_orthogonal_eq_zero {d : ℕ} {U : Submodule ℝ (E d)} {x : E d}
    (hx : x ∈ U) : Uᗮ.starProjection x = 0 := by
  have h1 : U.starProjection x = x :=
    (Submodule.starProjection_eq_self_iff).mpr hx
  have h2 : Uᗮ.starProjection x =
      (ContinuousLinearMap.id ℝ (E d) - U.starProjection) x :=
    DFunLike.congr_fun (Submodule.starProjection_orthogonal U) x
  rw [sub_apply, ContinuousLinearMap.id_apply, h1] at h2
  simpa using h2

/-- **The projected image of a completion is the `ℤ`-span of the projected tail.**  If
`u` spans `V` and `u ++ y` spans `W` (both over `ℤ`, e.g. from the aligned families), then

`W.map (projMap V) = span ℤ (range (fun j => (realSpan V)ᗮ.starProjection (y j)))`. -/
lemma map_projMap_eq_span_starProjection {d m b : ℕ} (V W : Submodule ℤ (E d))
    (u : Fin m → E d) (y : Fin b → E d)
    (huV : Submodule.span ℤ (Set.range u) = V)
    (huyW : Submodule.span ℤ (Set.range (Fin.append u y)) = W) :
    W.map (projMap V) =
      Submodule.span ℤ (Set.range (fun j => (realSpan V)ᗮ.starProjection (y j))) := by
  have hrealV : realSpan V = Submodule.span ℝ (Set.range u) := by
    rw [← huV]
    exact realSpan_span_range u
  have hmap : W.map (projMap V) = Submodule.span ℤ
      (Set.range (fun i : Fin (m + b) => projMap V (Fin.append u y i))) := by
    rw [← huyW, Submodule.map_span]
    congr 1
    exact (Set.range_comp (projMap V) (Fin.append u y)).symm
  rw [hmap]
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro z ⟨i, rfl⟩
    rcases fin_eq_castAdd_or_natAdd (m := m) (a := b) i with ⟨i₀, rfl⟩ | ⟨j, rfl⟩
    · simp only [Fin.append_left, projMap_apply, hrealV]
      rw [starProjection_orthogonal_eq_zero (U := Submodule.span ℝ (Set.range u))
        (Submodule.subset_span ⟨i₀, rfl⟩)]
      exact Submodule.zero_mem _
    · simp only [Fin.append_right, projMap_apply, hrealV]
      exact Submodule.subset_span ⟨j, rfl⟩
  · rw [Submodule.span_le]
    rintro z ⟨j, rfl⟩
    refine Submodule.subset_span ⟨Fin.natAdd m j, ?_⟩
    simp only [Fin.append_right, projMap_apply, hrealV]

/-- **The projected-quotient covolume factorisation (saturated-pair form).**  For a
full-rank lattice `Λ ≤ ℝᵈ` and nested saturated nonzero subgroups `V ≤ W ≤ Λ` with
`subDim V < subDim W`, the quottom lattice `Q := W.map (projMap V) ⊆ (realSpan V)ᗮ`
satisfies the exact factorisation

`latticeCovol W = latticeCovol V · latticeCovol Q`. -/
theorem latticeCovol_eq_mul_map_projMap {d : ℕ} (Λ V W : Submodule ℤ (E d))
    [DiscreteTopology Λ] [IsZLattice ℝ Λ] (hΛfin : Module.finrank ℤ Λ = d)
    (hVΛ : V ≤ Λ) (hWΛ : W ≤ Λ) (hVW : V ≤ W) (hV0 : V ≠ ⊥) (hW0 : W ≠ ⊥)
    (hVsat : Saturated Λ V) (hWsat : Saturated Λ W) (hrank : subDim V < subDim W) :
    latticeCovol W = latticeCovol V * latticeCovol (W.map (projMap V)) := by
  classical
  obtain ⟨m, _a, b, u, _x, y, huN, _huxV, huyW, _huxyS, hliRu, _hliRux, hliRuy, _hliRuxy⟩ :=
    exists_aligned_ambient_of_saturated_pair Λ V W hΛfin hVΛ hWΛ hV0 hW0 hVsat hWsat
  have hinf : V ⊓ W = V := inf_eq_left.mpr hVW
  have huV : Submodule.span ℤ (Set.range u) = V := by rw [huN, hinf]
  have hsubV : subDim V = m := by
    rw [← huV]
    exact subDim_span_range_of_linearIndependent u hliRu
  have hsubW : subDim W = m + b := by
    rw [← huyW]
    exact subDim_span_range_of_linearIndependent _ hliRuy
  have hm : 0 < m := by
    have h : subDim V ≠ 0 := fun hz => hV0 ((subDim_eq_zero_iff_bot V).mp hz)
    omega
  have hb : 0 < b := by omega
  have hrealV : realSpan V = Submodule.span ℝ (Set.range u) := by
    rw [← huV]
    exact realSpan_span_range u
  have hrealV : realSpan V = Submodule.span ℝ (Set.range u) := by
    rw [← huV]
    exact realSpan_span_range u
  have hmain : latticeCovol W = latticeCovol (Submodule.span ℤ (Set.range u)) *
      latticeCovol (Submodule.span ℤ (Set.range
        (fun j => (realSpan V)ᗮ.starProjection (y j)))) := by
    rw [← huyW]
    refine (latticeCovol_append_eq_mul_latticeCovol_starProjection (d := d) (m := m) (b := b)
      hm hb u y hliRu hliRuy).trans ?_
    congr 1
    rw [hrealV]
  -- identify the projected lattice with `W.map (projMap V)`
  rw [hmain, ← map_projMap_eq_span_starProjection V W u y huV huyW, huV]

end Submission.QuotientCovol

/-
  Area C2 (WilC2): the boundary set `{x | IsBnd D x}` of a definable set `D` is definable over the
  same parameters.

  The complement of `IsBnd D` is the union of `Int D` and `Int Dᶜ`, where
  `Int D = {x | ∃ a b, a < x ∧ x < b ∧ Ioo a b ⊆ D}` is the interior of `D`.  Both are definable:
  the order is `LRc`-definable via `definable_le` (every nonnegative element of a model of `TR` is a
  square), and all the conditions involve assignments only, so only `inter`, `compl`,
  `preimage_comp` and `exists_of_finite` (and their `Fin`-index bookkeeping) are needed.
-/
import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.BndDefs
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.finite_definable_singleton

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc TR rexpL)

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-- The strict-order set is definable. -/
lemma definable_lt {A : Set M} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z) {α : Type*}
    (i j : α) : A.Definable LRc {v : α → M | v i < v j} := by
  have h : {v : α → M | v j ≤ v i}ᶜ = {v : α → M | v i < v j} := by
    ext v
    exact not_le
  rw [← h]
  exact (definable_le (A := A) hsq j i).compl

/-- The set of points lying in an open interval contained in `D` (the "interior" of `D`, in the
`∃ a b` form). -/
def InteriorSet (D : Set M) : Set M :=
  {x : M | ∃ a b : M, a < x ∧ x < b ∧ Set.Ioo a b ⊆ D}

/-- The interior of a definable set is definable over the same parameters. -/
lemma definable_interior {A D : Set M} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hD : A.Definable LRc {v : Fin 1 → M | v 0 ∈ D}) :
    A.Definable LRc {v : Fin 1 → M | v 0 ∈ InteriorSet D} := by
  classical
  -- `x` is `Sum.inl 0`, `a` is `Sum.inr 0`, `b` is `Sum.inr 1`
  have hlt1 : A.Definable LRc {v : Fin 1 ⊕ Fin 2 → M | v (Sum.inr (0 : Fin 2)) < v (Sum.inl 0)} :=
    definable_lt hsq (Sum.inr (0 : Fin 2)) (Sum.inl (0 : Fin 1))
  have hlt2 : A.Definable LRc {v : Fin 1 ⊕ Fin 2 → M | v (Sum.inl (0 : Fin 1)) < v (Sum.inr 1)} :=
    definable_lt hsq (Sum.inl (0 : Fin 1)) (Sum.inr (1 : Fin 2))
  -- the "bad" set of quadruples `(x, a, b, z)` with `z ∈ Ioo a b` and `z ∉ D`
  have hnotD : A.Definable LRc {w : (Fin 1 ⊕ Fin 2) ⊕ Fin 1 → M |
      w (Sum.inr (0 : Fin 1)) ∉ D} := by
    have hc : A.Definable LRc {u : Fin 1 → M | u 0 ∉ D} := by
      have h' := hD.compl
      rwa [Set.compl_setOf] at h'
    have := hc.preimage_comp (fun _ : Fin 1 => (Sum.inr (0 : Fin 1) : (Fin 1 ⊕ Fin 2) ⊕ Fin 1))
    convert this using 2
    ext w
    simp [Function.comp_apply]
  have hbad : A.Definable LRc {w : (Fin 1 ⊕ Fin 2) ⊕ Fin 1 → M |
      w (Sum.inr (0 : Fin 1)) < w (Sum.inl (Sum.inr 1)) ∧
      w (Sum.inl (Sum.inr 0)) < w (Sum.inr (0 : Fin 1)) ∧
      w (Sum.inr (0 : Fin 1)) ∉ D} := by
    have h1 : A.Definable LRc {w : (Fin 1 ⊕ Fin 2) ⊕ Fin 1 → M |
        w (Sum.inr (0 : Fin 1)) < w (Sum.inl (Sum.inr 1))} :=
      definable_lt hsq (Sum.inr (0 : Fin 1)) (Sum.inl (Sum.inr (1 : Fin 2)))
    have h2 : A.Definable LRc {w : (Fin 1 ⊕ Fin 2) ⊕ Fin 1 → M |
        w (Sum.inl (Sum.inr 0)) < w (Sum.inr (0 : Fin 1))} :=
      definable_lt hsq (Sum.inl (Sum.inr (0 : Fin 2))) (Sum.inr (0 : Fin 1))
    have h := (h1.inter h2).inter hnotD
    convert h using 2
    ext w
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  -- the `∀ z` clause: `Ioo a b ⊆ D`
  have hsub : A.Definable LRc {v : Fin 1 ⊕ Fin 2 → M |
      Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ D} := by
    have h := (hbad.compl).forall_of_finite (α := Fin 1 ⊕ Fin 2) (β := Fin 1)
    have hset : {v : Fin 1 ⊕ Fin 2 → M | ∀ u : Fin 1 → M, Sum.elim v u ∈
        ({w : (Fin 1 ⊕ Fin 2) ⊕ Fin 1 → M |
          w (Sum.inr (0 : Fin 1)) < w (Sum.inl (Sum.inr 1)) ∧
          w (Sum.inl (Sum.inr 0)) < w (Sum.inr (0 : Fin 1)) ∧
          w (Sum.inr (0 : Fin 1)) ∉ D})ᶜ} =
        {v : Fin 1 ⊕ Fin 2 → M | Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ D} := by
      ext v
      constructor
      · intro hv x hx
        by_contra hxD
        have hbad' : (Sum.elim v (fun _ : Fin 1 => x)) ∈
            ({w : (Fin 1 ⊕ Fin 2) ⊕ Fin 1 → M |
              w (Sum.inr (0 : Fin 1)) < w (Sum.inl (Sum.inr 1)) ∧
              w (Sum.inl (Sum.inr 0)) < w (Sum.inr (0 : Fin 1)) ∧
              w (Sum.inr (0 : Fin 1)) ∉ D}) := by
          simp only [Set.mem_ofPred_eq]
          exact ⟨hx.2, hx.1, hxD⟩
        exact (hv (fun _ => x)) hbad'
      · intro hv u
        rintro ⟨h1, h2, h3⟩
        exact h3 (hv ⟨h2, h1⟩)
    rw [hset] at h
    exact h
  -- assemble the triple set and project out `a`, `b`
  have htriple : A.Definable LRc {v : Fin 1 ⊕ Fin 2 → M |
      v (Sum.inr 0) < v (Sum.inl 0) ∧ v (Sum.inl 0) < v (Sum.inr 1) ∧
        Set.Ioo (v (Sum.inr 0)) (v (Sum.inr 1)) ⊆ D} := by
    have h := (hlt1.inter hlt2).inter hsub
    convert h using 2
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  have hproj := htriple.exists_of_finite (α := Fin 1) (β := Fin 2)
  have hset : {v : Fin 1 → M | ∃ u : Fin 2 → M,
        (Sum.elim v u) ∈ {w : Fin 1 ⊕ Fin 2 → M |
          w (Sum.inr 0) < w (Sum.inl 0) ∧ w (Sum.inl 0) < w (Sum.inr 1) ∧
            Set.Ioo (w (Sum.inr 0)) (w (Sum.inr 1)) ⊆ D}} =
      {v : Fin 1 → M | v 0 ∈ InteriorSet D} := by
    ext v
    constructor
    · rintro ⟨u, h1, h2, h3⟩
      exact ⟨u 0, u 1, h1, h2, h3⟩
    · rintro ⟨a, b, h1, h2, h3⟩
      refine ⟨![a, b], ?_, ?_, ?_⟩
      · simpa using h1
      · simpa using h2
      · simpa using h3
  rw [hset] at hproj
  exact hproj

/-- The `∃ ε` form of the interior. -/
lemma exists_Ioo_subset_iff_interior {D : Set M} {x : M} :
    (∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D) ↔ x ∈ InteriorSet D := by
  constructor
  · rintro ⟨ε, hε, hsub⟩
    exact ⟨x - ε, x + ε, by linarith [hε], by linarith [hε], hsub⟩
  · rintro ⟨a, b, hax, hxb, hsub⟩
    refine ⟨min (x - a) (b - x), lt_min (by linarith) (by linarith), ?_⟩
    have h1 : min (x - a) (b - x) ≤ x - a := min_le_left _ _
    have h2 : min (x - a) (b - x) ≤ b - x := min_le_right _ _
    intro y hy
    exact hsub ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- **The boundary set of a definable set is definable.** -/
theorem bnd_definable_alt {A D : Set M} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (hD : A.Definable LRc {v : Fin 1 → M | v 0 ∈ D}) :
    A.Definable LRc {v : Fin 1 → M | IsBnd D (v 0)} := by
  have h1 : A.Definable LRc {v : Fin 1 → M | v 0 ∈ InteriorSet D} := definable_interior hsq hD
  have hDc : A.Definable LRc {v : Fin 1 → M | v 0 ∈ Dᶜ} := by
    have h' := hD.compl
    rwa [Set.compl_setOf] at h'
  have h2 : A.Definable LRc {v : Fin 1 → M | v 0 ∈ InteriorSet Dᶜ} :=
    definable_interior hsq hDc
  have h3 : A.Definable LRc {v : Fin 1 → M |
      v 0 ∉ InteriorSet D ∧ v 0 ∉ InteriorSet Dᶜ} := by
    have h := (h1.union h2).compl
    convert h using 2
    ext v
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or]
  have hgoal : {v : Fin 1 → M | v 0 ∉ InteriorSet D ∧ v 0 ∉ InteriorSet Dᶜ} =
      {v : Fin 1 → M | IsBnd D (v 0)} := by
    ext v
    simp only [Set.mem_ofPred_eq]
    rw [IsBnd]
    constructor
    · rintro ⟨h1', h2'⟩
      exact ⟨fun h => h1' ((exists_Ioo_subset_iff_interior).mp h),
        fun h => h2' ((exists_Ioo_subset_iff_interior).mp h)⟩
    · rintro ⟨h1', h2'⟩
      exact ⟨fun h => h1' ((exists_Ioo_subset_iff_interior).mpr h),
        fun h => h2' ((exists_Ioo_subset_iff_interior).mpr h)⟩
  rwa [hgoal] at h3

end Work.WilC2

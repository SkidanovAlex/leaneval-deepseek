/-
  Area C2 (WilC2): the *exchange property* of the definable closure.

  In an o-minimal structure the definable closure of a set satisfies the Steinitz exchange axiom:
  if `a` is definable from `A ∪ {b}` but not from `A`, then `b` is definable from `A ∪ {a}`.

  The proof runs as follows.  Put `T := Dcl A` (a `dcl`-closed set, hence an elementary
  substructure by Tarski--Vaught) and let `R` be a `T`-definable partial function whose fibre over
  `b` is the singleton `{a}` (this is what `a ∈ Dcl (insert b A)` supplies, after moving the
  parameter `b` into a variable slot).  Suppose, for contradiction, that `b ∉ Dcl (insert a T)`.
  The set `W := {y | R y a}` is definable over `insert a T` and contains `b`, so `b` lies in the
  interior of `W` (boundary points of definable sets are definable: they are finitely many, and
  the elements of a finite definable set are definable).  Hence `R` is locally constant at `b`, and
  `b` belongs to the `T`-definable set `H` of points at which `R` is locally constant.  Since `b`
  is not `T`-definable, `H` contains a `T`-point `r` in the same convex component of `H` as `b`
  (`window_point_mem_dcl`), and local constancy forces the value of `R` at `r` to be `a`
  (`value_const_on_window2`, which is where definable completeness of models of `TR` enters).
  Finally `r ∈ Dcl A` makes the singleton `{x | R r x} = {a}` definable over `Dcl A`, so
  `a ∈ Dcl A`, contradicting the hypothesis.
-/
import Mathlib
import Submission.Work.WilC2.Dcl
import Submission.Work.WilC2.Main
import Submission.Work.WilC2.Uniform
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC2.Square
import Submission.Work.WilC2.BndDefs
import Submission.Work.WilC2.boundary_finite
import Submission.Work.WilC2.bnd_definable_alt
import Submission.Work.WilC2.finite_definable_singleton
import Submission.Work.WilC2.fibre_definable
import Submission.Work.WilC2.fibre_definable_fst
import Submission.Work.WilC2.relabel_graph_aux
import Submission.Work.WilC2.definable_constancy_set2
import Submission.Work.WilC2.value_const_on_window2
import Submission.Work.WilC2.window_aux_self

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open WilkiesDesign.CG (LR LRc TR rexpL)

namespace Work.WilC2

/-! ## Glue for the definable closure -/

section Glue

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [FirstOrder.Ring.CompatibleRing M] [rexpL.Structure M]
  [(FirstOrder.Language.constantsOn ℝ).Structure M]

/-- Every element of a parameter set is definable from it. -/
lemma subset_dcl_aux (A : Set M) : A ⊆ Dcl A :=
  fun a ha => mem_dcl.mpr (Set.Definable.singleton_of_mem (L := LRc) ha)

/-- Closing a parameter set together with an extra element `b`, and then closing again, changes
nothing: `Dcl (insert b A) = Dcl (insert b (Dcl A))`. -/
lemma dcl_insert_dcl (A : Set M) (b : M) :
    Dcl (insert b A) = Dcl (insert b (Dcl A)) := by
  refine le_antisymm ?_ ?_
  · exact dcl_mono (Set.insert_subset_insert (subset_dcl_aux A))
  · have h1 : Dcl A ⊆ Dcl (insert b A) := dcl_mono (Set.subset_insert b A)
    have h2 : b ∈ Dcl (insert b A) := subset_dcl_aux (insert b A) (Set.mem_insert b A)
    have h3 : insert b (Dcl A) ⊆ Dcl (insert b A) := Set.insert_subset h2 h1
    have h4 : Dcl (insert b (Dcl A)) ⊆ Dcl (Dcl (insert b A)) := dcl_mono h3
    rwa [dcl_idem] at h4

/-- **Boundary points of a definable set are definable.**  If `D` is `A`-definable in a model of
`TR` and `x ∈ D` is not definable from `A`, then `x` is an interior point of `D`. -/
lemma exists_Ioo_subset_of_mem_of_not_mem_dcl
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable LRc X → RExpExist X)
    (hUF : UnifFiniteRExp) [M ⊨ TR]
    {A : Set M} {D : Set M} (hD : A.Definable LRc {v : Fin 1 → M | v 0 ∈ D})
    {x : M} (hx : x ∈ D) (hxA : x ∉ Dcl A) :
    ∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D := by
  classical
  have hsq : ∀ y : M, 0 ≤ y → ∃ z : M, y = z * z := model_exists_sq ‹M ⊨ TR›
  -- the boundary set of `D` is definable and finite, hence consists of definable elements
  have hBdef : A.Definable₁ LRc ({y : M | IsBnd D y} : Set M) := by
    show A.Definable LRc {v : Fin 1 → M | v 0 ∈ ({y : M | IsBnd D y} : Set M)}
    exact bnd_definable_alt hsq hD
  obtain ⟨F, hF⟩ := boundary_finite (M := M) hR hC0 hUF hD
  have hfin : {y : M | IsBnd D y}.Finite :=
    F.finite_toSet.subset (fun y hy => hF y hy.1 hy.2)
  have hsub : {y : M | IsBnd D y} ⊆ Dcl A := fun y hy =>
    mem_dcl.mpr (finite_definable_singleton ‹M ⊨ TR› hBdef hfin y hy)
  have hxnot : ¬ IsBnd D x := fun hb => hxA (hsub hb)
  -- `¬ IsBnd D x` splits into the two alternatives defining `IsBnd`
  have hdisj : (∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ D) ∨
      (∃ ε : M, 0 < ε ∧ Set.Ioo (x - ε) (x + ε) ⊆ Dᶜ) := by
    by_contra hc
    exact hxnot ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩
  rcases hdisj with ⟨ε, hε, hsub'⟩ | ⟨ε, hε, hsub'⟩
  · exact ⟨ε, hε, hsub'⟩
  · exfalso
    exact hsub' (mem_Ioo_self hε) hx

end Glue

/-! ## The exchange property -/

theorem dcl_exchange
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hC0 : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc X → WilkiesDesign.RExpExist X)
    (hUF : WilkiesDesign.CG.UnifFiniteRExp)
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M]
    [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [M ⊨ WilkiesDesign.CG.TR] (A : Set M) {a b : M}
    (h : a ∈ Dcl (insert b A)) (ha : a ∉ Dcl A) :
    b ∈ Dcl (insert a A) := by
  classical
  -- `b` is not definable from `A`: otherwise `insert b A ⊆ Dcl A` and `a ∈ Dcl (Dcl A) = Dcl A`
  have hbA : b ∉ Dcl A := by
    intro hb
    refine ha ?_
    have h2 : a ∈ Dcl (Dcl A) :=
      dcl_mono (Set.insert_subset hb (subset_dcl_aux A)) h
    rwa [dcl_idem] at h2
  -- move `b` from the parameter set into a variable slot: `{a}` is definable over `insert b T`
  have h1 : (insert b (Dcl A)).Definable LRc {v : Fin 1 → M | v 0 ∈ ({a} : Set M)} := by
    have hh : (insert b A).Definable LRc {v : Fin 1 → M | v 0 ∈ ({a} : Set M)} := mem_dcl.mp h
    exact hh.mono (Set.insert_subset_insert (subset_dcl_aux A))
  -- a `Dcl A`-definable partial function with value `a` at `b`
  obtain ⟨R, hRdef, hRfib, hRgraph⟩ := exists_relabel_graph_aux (M := M) hR hC0 hUF h1
  -- it suffices to work with the parameter set `insert a (Dcl A)`
  have hmain : b ∈ Dcl (insert a (Dcl A)) := by
    -- suppose `b` is not definable from `Dcl A ∪ {a}`
    by_contra hbU
    -- the set `W = {y | R y a}` is definable over `insert a (Dcl A)` and contains `b`
    let W : Set M := {y | R y a}
    have hWdef : (insert a (Dcl A)).Definable LRc {v : Fin 1 → M | v 0 ∈ W} := by
      have hG : (Dcl A).Definable LRc {v : Fin 2 → M | R (v 0) (v 1)} := hRdef
      have hfib := fibre_definable (A := Dcl A) hG (u := a)
      have hset : {v : Fin 1 → M |
          (fun i : Fin 2 => if i = 0 then v 0 else a) ∈ {w : Fin 2 → M | R (w 0) (w 1)}}
          = {v : Fin 1 → M | v 0 ∈ W} := by
        ext v
        simp only [Set.mem_ofPred_eq]
        constructor
        · intro hv
          simpa [W, Fin.isValue] using hv
        · intro hv
          simpa [W, Fin.isValue] using hv
      rw [hset] at hfib
      refine hfib.mono ?_
      rintro y (hy | hy)
      · exact Set.mem_insert_of_mem a hy
      · rw [Set.mem_singleton_iff] at hy
        rw [Set.mem_insert_iff]
        exact Or.inl hy
    have hbW : b ∈ W := (hRfib a).mpr rfl
    -- hence `b` is an interior point of `W`: `R` is locally constant at `b`
    obtain ⟨ε, hε, hεsub⟩ :=
      exists_Ioo_subset_of_mem_of_not_mem_dcl (M := M) hR hC0 hUF hWdef hbW hbU
    -- the `Dcl A`-definable set of points where `R` is locally constant contains `b`
    let H : Set M := {y | (∃ x : M, R y x) ∧
      ∃ ε : M, 0 < ε ∧ ∀ z : M, y - ε < z → z < y + ε → ∀ x : M, R y x → R z x}
    have hHdef : (Dcl A).Definable LRc {v : Fin 1 → M | v 0 ∈ H} :=
      definable_constancy_set2 (M := M) (model_exists_sq ‹M ⊨ TR›) hRdef
    have hbH : b ∈ H := by
      refine ⟨⟨a, (hRfib a).mpr rfl⟩, ε, hε, ?_⟩
      intro z hz1 hz2 x hx
      obtain rfl : x = a := (hRfib x).mp hx
      exact hεsub ⟨hz1, hz2⟩
    -- a `Dcl A`-point in the same convex component of `H` as `b`
    have hbA' : b ∉ Dcl (Dcl A) := by simpa [dcl_idem A] using hbA
    obtain ⟨r, hrDcl, hrwin⟩ :=
      window_point_aux_self (M := M) hR hC0 hUF (A := Dcl A) hHdef hbH hbA'
    have hrA : r ∈ Dcl A := by
      have h' := hrDcl
      rwa [dcl_idem] at h'
    have hrH : r ∈ H := hrwin (Set.mem_Icc.mpr ⟨min_le_left r b, le_max_left r b⟩)
    have hneH : ∀ y ∈ H, ∃ x : M, R y x := fun y hy => hy.1
    have hlocH : ∀ y ∈ H, ∃ ε : M,
        0 < ε ∧ ∀ z ∈ Set.Ioo (y - ε) (y + ε), z ∈ H → ∀ x : M, R y x → R z x := by
      rintro y ⟨-, ε, hε, hrest⟩
      exact ⟨ε, hε, fun z hz _ x hx => hrest z hz.1 hz.2 x hx⟩
    -- local constancy on the component: the value of `R` at `r` is `a`
    have hrval : ∀ x : M, R r x → x = a := by
      intro x hx
      obtain ⟨x₀, hx₀⟩ := hneH r hrH
      have hax₀ : a = x₀ :=
        value_const_on_window2 (M := M) hR hC0 hUF (T := Dcl A) (H := H) (P := R)
          (le_of_eq (dcl_idem A)) hHdef hRdef hneH
          (fun y _ x x' hx hx' => hRgraph y x x' hx hx') hlocH hbH hrH
          (by simpa [min_comm, max_comm] using hrwin) ((hRfib a).mpr rfl) hx₀
      rw [hRgraph r x x₀ hx hx₀]
      exact hax₀.symm
    have hra : R r a := by
      obtain ⟨x₀, hx₀⟩ := hneH r hrH
      rwa [hrval x₀ hx₀] at hx₀
    -- `{x | R r x} = {a}` is `Dcl A`-definable, so `a ∈ Dcl A`
    have hset2 : {v : Fin 1 → M |
        (fun i : Fin 2 => if i = 0 then r else v 0) ∈ {w : Fin 2 → M | R (w 0) (w 1)}}
        = {v : Fin 1 → M | v 0 ∈ ({a} : Set M)} := by
      ext v
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hv
        exact hrval (v 0) (by simpa using hv)
      · intro hv
        rw [hv]
        simpa using hra
    have haT : a ∈ Dcl A := by
      have hG : (Dcl A).Definable LRc {v : Fin 2 → M | R (v 0) (v 1)} := hRdef
      have hfib := fibre_definable_fst (A := Dcl A) hG (u := r)
      have hsub : Dcl A ∪ {r} ⊆ Dcl A := by
        refine Set.union_subset (subset_refl _) ?_
        rw [Set.singleton_subset_iff]
        exact hrA
      have h3 : (Dcl A).Definable LRc {v : Fin 1 → M |
          (fun i : Fin 2 => if i = 0 then r else v 0) ∈ {w : Fin 2 → M | R (w 0) (w 1)}} :=
        hfib.mono hsub
      rw [hset2] at h3
      have h3' : (Dcl A).Definable₁ LRc ({a} : Set M) := by
        show (Dcl A).Definable LRc {v : Fin 1 → M | v 0 ∈ ({a} : Set M)}
        exact h3
      have h4 : a ∈ Dcl (Dcl A) := mem_dcl.mpr h3'
      rwa [dcl_idem] at h4
    exact ha haT
  rwa [← dcl_insert_dcl A a] at hmain

end Work.WilC2

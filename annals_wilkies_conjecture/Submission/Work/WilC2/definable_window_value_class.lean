/-
  Area C2 (WilC2): `definable_window_value_class`.

  Let `M ⊨ TR`, let `P : M → M → Prop` be definable in `LRc` over some parameter set `T ⊆ M`
  (this is `hP`; note that `Definable` asks for a formula with *constants* from `T`, and it
  suffices for the whole relation, not just for its restriction to `T × M`).  Then, for any two
  points `y y' : M`, the window `[min y y', max y y']` spanned by them and the "value class"

  `{z : M | z ∈ [min y y', max y y'] ∧ ∃ w : M, P y w ∧ P z w}`

  are `LRc`-definable over the parameter set `univ` (i.e. with arbitrary parameters).

  Mathematically there is nothing to it beyond the two closure properties of `Definable`:

  * the order of `M` is `LRc`-definable, because in a model of `TR` every nonnegative element is
    a square (`Work.WilC2.model_exists_sq`), so that `x ≤ y` is the ring formula
    `∃ z, x + z * z = y` (`Work.WilC2.definable_le`).  Hence `{x | x ∈ [a,b]}` is definable, and
    pulling it back along the definable map `v ↦ ![min y y', v 0, max y y']` gives the window.
  * the relation `P` is definable over `T`, hence over `univ` (`Definable.mono`); forming the
    conjunction `P (v 0) u ∧ P (v 1) u`, quantifying the common witness `u` out
    (`Definable.exists_of_finite`), and pulling back along the definable map `v ↦ ![y, v 0]`
    (`Set.Definable.preimage_map`) gives `{z | ∃ w, P y w ∧ P z w}`.

  The parameter set `univ` is exactly what allows the *free* points `y`, `y'` of the statement to
  be used as constants; the hypothesis `hP` only enters through `Definable.mono`, which enlarges
  the parameter set `T` to `univ`.
-/
import Mathlib
import Submission.Work.WilC2.finite_definable_singleton

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-! ## Two reusable closure lemmas -/

/-- **The window spanned by two points is definable.**  In a model of `TR`, for any two points
`a b : M` the interval `[a,b]` is `LRc`-definable over the parameter set `univ`.

The order is definable by `Work.WilC2.definable_le` (every nonnegative element of a model of `TR`
is a square), and `[a,b]` is the preimage of `{w : Fin 3 → M | w 0 ≤ w 1 ∧ w 1 ≤ w 2}` under the
definable map `v ↦ ![a, v 0, b]` (`Set.Definable.preimage_map`). -/
lemma definable_Icc_univ
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR)
    (a b : M) :
    (Set.univ : Set M).Definable₁ LRc (Set.Icc a b) := by
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  have hle1 : (Set.univ : Set M).Definable LRc {w : Fin 3 → M | w 0 ≤ w 1} :=
    definable_le (A := Set.univ) hsq 0 1
  have hle2 : (Set.univ : Set M).Definable LRc {w : Fin 3 → M | w 1 ≤ w 2} :=
    definable_le (A := Set.univ) hsq 1 2
  have hS : (Set.univ : Set M).Definable LRc
      {w : Fin 3 → M | w 0 ≤ w 1 ∧ w 1 ≤ w 2} := hle1.inter hle2
  have hF : (Set.univ : Set M).DefinableMap LRc (fun v : Fin 1 → M => ![a, v 0, b]) := by
    intro i
    fin_cases i
    · simpa using (FirstOrder.Language.definableFun_const (L := LRc) (A := (Set.univ : Set M))
        (a := a) (Fin 1) (Set.mem_univ _))
    · simpa using (Set.DefinableFun.proj (L := LRc) (A := (Set.univ : Set M)) (α := Fin 1) (i := 0))
    · simpa using (FirstOrder.Language.definableFun_const (L := LRc) (A := (Set.univ : Set M))
        (a := b) (Fin 1) (Set.mem_univ _))
  have h := hS.preimage_map hF
  have hset : ((fun v : Fin 1 → M => ![a, v 0, b]) ⁻¹'
      {w : Fin 3 → M | w 0 ≤ w 1 ∧ w 1 ≤ w 2}) =
      {v : Fin 1 → M | v 0 ∈ Set.Icc a b} := by
    ext v
    simp [Set.mem_Icc]
  unfold Set.Definable₁
  rw [← hset]
  exact h

/-- **The value class of `y` is definable.**  If the relation `P` is `LRc`-definable over some
parameter set `T ⊆ M`, then for every `y : M` the set `{z : M | ∃ w, P y w ∧ P z w}` of points
whose `P`-fibre meets the `P`-fibre of `y` is `LRc`-definable over `univ`.

This is the "class of points with the same value as `y`" of the window argument, stripped of the
window.  The only inputs are `Definable.mono` (to replace `T` by `univ`), closure under finite
projections `Definable.exists_of_finite`, and `Set.Definable.preimage_map` along the definable
map `v ↦ ![y, v 0]`. -/
lemma definable_valueClass_univ
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    {T : Set M} {P : M → M → Prop}
    (hP : T.Definable LRc {v : Fin 2 → M | P (v 0) (v 1)}) (y : M) :
    (Set.univ : Set M).Definable LRc {v : Fin 1 → M | ∃ w : M, P y w ∧ P (v 0) w} := by
  -- `P` is definable over all of `M`, since `T ⊆ univ`
  have hQ : (Set.univ : Set M).Definable LRc {v : Fin 2 → M | P (v 0) (v 1)} :=
    hP.mono (Set.subset_univ T)
  -- `P (t (inl 0)) (t (inr 0))` on `(Fin 2 ⊕ Fin 1) → M`, i.e. `P` read at the pair `(v 0, u)`
  have h1 : (Set.univ : Set M).Definable LRc
      {t : (Fin 2 ⊕ Fin 1) → M | P (t (Sum.inl 0)) (t (Sum.inr 0))} :=
    hQ.preimage_comp (fun i : Fin 2 => ![Sum.inl (0 : Fin 2), Sum.inr (0 : Fin 1)] i)
  -- the same with `(v 1, u)`
  have h2 : (Set.univ : Set M).Definable LRc
      {t : (Fin 2 ⊕ Fin 1) → M | P (t (Sum.inl 1)) (t (Sum.inr 0))} :=
    hQ.preimage_comp (fun i : Fin 2 => ![Sum.inl (1 : Fin 2), Sum.inr (0 : Fin 1)] i)
  -- quantify the common witness out
  have hpair : (Set.univ : Set M).Definable LRc
      {v : Fin 2 → M | ∃ u : M, P (v 0) u ∧ P (v 1) u} := by
    have h := (h1.inter h2).exists_of_finite (α := Fin 2) (β := Fin 1)
    have hset : {v : Fin 2 → M | ∃ u : Fin 1 → M,
          Sum.elim v u ∈ {t : (Fin 2 ⊕ Fin 1) → M | P (t (Sum.inl 0)) (t (Sum.inr 0))} ∩
            {t : (Fin 2 ⊕ Fin 1) → M | P (t (Sum.inl 1)) (t (Sum.inr 0))}} =
        {v : Fin 2 → M | ∃ u : M, P (v 0) u ∧ P (v 1) u} := by
      ext v
      constructor
      · rintro ⟨u, hu1, hu2⟩
        exact ⟨u 0, hu1, hu2⟩
      · rintro ⟨u, hu1, hu2⟩
        exact ⟨fun _ => u, hu1, hu2⟩
    rw [hset] at h
    exact h
  -- fix the first coordinate at the parameter `y`
  have hF : (Set.univ : Set M).DefinableMap LRc (fun v : Fin 1 → M => ![y, v 0]) := by
    intro i
    fin_cases i
    · simpa using (FirstOrder.Language.definableFun_const (L := LRc) (A := (Set.univ : Set M))
        (a := y) (Fin 1) (Set.mem_univ _))
    · simpa using (Set.DefinableFun.proj (L := LRc) (A := (Set.univ : Set M)) (α := Fin 1) (i := 0))
  have h := hpair.preimage_map hF
  have hset : ((fun v : Fin 1 → M => ![y, v 0]) ⁻¹'
      {v : Fin 2 → M | ∃ u : M, P (v 0) u ∧ P (v 1) u}) =
      {v : Fin 1 → M | ∃ w : M, P y w ∧ P (v 0) w} := by
    ext v
    simp
  rw [hset] at h
  exact h

/-! ## The target lemma -/

theorem definable_window_value_class
    {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR)
    {T : Set M} {P : M → M → Prop}
    (hP : T.Definable WilkiesDesign.CG.LRc {v : Fin 2 → M | P (v 0) (v 1)})
    (y y' : M) :
    (Set.univ : Set M).Definable₁ WilkiesDesign.CG.LRc (Set.Icc (min y y') (max y y')) ∧
      (Set.univ : Set M).Definable₁ WilkiesDesign.CG.LRc
        {z : M | z ∈ Set.Icc (min y y') (max y y') ∧ ∃ w : M, P y w ∧ P z w} := by
  refine ⟨definable_Icc_univ hM (min y y') (max y y'), ?_⟩
  have hIcc : (Set.univ : Set M).Definable LRc
      {v : Fin 1 → M | v 0 ∈ Set.Icc (min y y') (max y y')} :=
    definable_Icc_univ hM (min y y') (max y y')
  have hVal : (Set.univ : Set M).Definable LRc
      {v : Fin 1 → M | ∃ w : M, P y w ∧ P (v 0) w} :=
    definable_valueClass_univ hP y
  have hgoal : (Set.univ : Set M).Definable LRc
      {v : Fin 1 → M | v 0 ∈ Set.Icc (min y y') (max y y') ∧ ∃ w : M, P y w ∧ P (v 0) w} := by
    rw [show {v : Fin 1 → M | v 0 ∈ Set.Icc (min y y') (max y y') ∧ ∃ w : M, P y w ∧ P (v 0) w} =
        {v : Fin 1 → M | v 0 ∈ Set.Icc (min y y') (max y y')} ∩
          {v : Fin 1 → M | ∃ w : M, P y w ∧ P (v 0) w} from by
      ext v
      simp]
    exact hIcc.inter hVal
  exact hgoal

end Work.WilC2

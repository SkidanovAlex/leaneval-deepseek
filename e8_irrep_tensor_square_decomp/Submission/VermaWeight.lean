import Submission.VermaNonzero
import Submission.WeightIndependence
import Submission.EnvelopingModule
import Submission.Commons.Algebra.Module.exists_max_submodule_notMem
import Submission.Commons.RepresentationTheory.LieEnveloping.isIrreducible_iff_isSimpleModule
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-!
# The weight-graded structure of the Verma module `V = A/J`

`V = FA (Fin 8) / J` (see `Submission.StarQuotient`) carries an `e₈`-module structure
(`Submission.VermaNonzero.act`) turning `v = 1 + J` into a highest weight vector of weight
`λ = ω₁ + ω₈`.  This file proves the weight-graded structure of `V`:

* `Wm m` is the span of the word vectors `mk (wordElt w)` whose letters have multiplicity vector
  `m`; the `Wm m` span `V` (`iSup_Wm_eq_top`) and `Hbar i` acts on `Wm m` by the scalar
  `wtVec m i` (`Hbar_apply_mem_Wm`);
* every element of `V` is a finite sum of elements of the `Wm m` (`exists_decomp`);
* **consequently every `ρ`-stable subspace, in particular every `U(e₈)`-submodule, is the direct
  sum of its intersections with the `Wm m`** (`component_mem_of_stable`);
* the `λ`-weight space is one-dimensional (`Wm_zero_eq`) so the sum of two proper submodules is
  proper (`sup_ne_top_of_ne_top_of_ne_top`), and hence `V` has a unique maximal submodule with
  simple quotient `L(λ) ≠ 0`, a highest weight module of weight `λ`
  (`exists_irreducible_highest_weight`).
-/

set_option maxHeartbeats 1000000

noncomputable section
open scoped BigOperators

namespace Submission.VermaWeight

open Submission.StarModule (FA wordElt Hop_apply Hword wrho wordElt_nil bas bas_apply)
open Submission.StarQuotient (Hbar Hbar_mk Ebar Ebar_mk)

abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

abbrev lam : Fin 8 → ℂ := Submission.E8Weights.omegaOnePlusOmegaEight

abbrev V : Type := Submission.StarQuotient.V E8

/-- The weight vector attached to a multiplicity vector `m`: `wtVec m i = λ i - ∑ a, m a * A i a`. -/
abbrev wt (m : Fin 8 → ℕ) : Fin 8 → ℂ := Submission.WeightIndependence.wtVec m

lemma wt_def (m : Fin 8 → ℕ) (i : Fin 8) :
    wt m i = lam i - ∑ a : Fin 8, (m a : ℂ) * (E8 i a : ℂ) := rfl

/-- The span of the word vectors with letter multiplicities `m`. -/
def Wm (m : Fin 8 → ℕ) : Submodule ℂ V :=
  Submodule.span ℂ {x : V | ∃ w : List (Fin 8), (∀ i, w.count i = m i) ∧
    x = (Submodule.Quotient.mk (wordElt w) : V)}

lemma mk_wordElt_mem_Wm (w : List (Fin 8)) :
    (Submodule.Quotient.mk (wordElt w) : V) ∈ Wm (fun i => w.count i) :=
  Submodule.subset_span ⟨w, fun _ => rfl, rfl⟩

/-- `Hbar i` acts on `Wm m` by the scalar `wt m i`. -/
lemma Hbar_apply_mem_Wm (i : Fin 8) {m : Fin 8 → ℕ} {x : V} (hx : x ∈ Wm m) :
    Hbar E8 lam i x = wt m i • x := by
  classical
  have hkey : ∀ (w : List (Fin 8)), (∀ k, w.count k = m k) →
      Hbar E8 lam i (Submodule.Quotient.mk (wordElt w) : V)
        = wt m i • (Submodule.Quotient.mk (wordElt w) : V) := by
    intro w hw
    have hscal : lam i - wrho E8 i w = wt m i := by
      rw [wt_def, wrho, Submission.WeightIndependence.sum_map_eq_sum_count]
      have hcount : ∀ k : Fin 8, w.count k = m k := fun k => hw k
      simp only [hcount]
    rw [Hbar_mk, Hop_apply, Hword, ← Submodule.Quotient.mk_smul, hscal]
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact hkey w hw
  | zero => rw [map_zero, smul_zero]
  | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | smul c x _ ih => rw [map_smul, ih, smul_comm]


/-- The word vectors `mk (wordElt w)` span `V`. -/
lemma span_mk_wordElt_eq_top :
    Submodule.span ℂ (Set.range (fun w : List (Fin 8) =>
      (Submodule.Quotient.mk (wordElt w) : V))) = ⊤ := by
  have hbas : Submodule.span ℂ (Set.range (fun w : List (Fin 8) => wordElt w)) = ⊤ := by
    have hrange : Set.range (fun w : List (Fin 8) => wordElt w) = Set.range (bas (Fin 8)) := by
      ext y
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨w, bas_apply w⟩
      · rintro ⟨w, rfl⟩; exact ⟨w, (bas_apply w).symm⟩
    rw [hrange]
    exact (bas (Fin 8)).span_eq
  have h1 : Submodule.map (Submodule.mkQ (Submission.StarQuotient.J E8))
      (Submodule.span ℂ (Set.range (fun w : List (Fin 8) => wordElt w)))
      = Submodule.span ℂ (Set.range (fun w : List (Fin 8) =>
          (Submodule.Quotient.mk (wordElt w) : V))) := by
    rw [Submodule.map_span]
    congr 1
    exact (Set.range_comp (Submodule.mkQ (Submission.StarQuotient.J E8))
      (fun w : List (Fin 8) => wordElt w)).symm
  rw [← h1, hbas, Submodule.map_top, LinearMap.range_eq_top]
  exact Submodule.mkQ_surjective _

/-- `V` is the supremum of the word spaces `Wm m`. -/
lemma iSup_Wm_eq_top : (⨆ m : Fin 8 → ℕ, Wm m) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← span_mk_wordElt_eq_top]
  refine Submodule.span_le.mpr ?_
  rintro x ⟨w, rfl⟩
  exact le_iSup (fun m : Fin 8 → ℕ => Wm m) (fun i => w.count i) (mk_wordElt_mem_Wm w)

/-- Every element of `V` is a finite sum of elements of the word spaces `Wm m`. -/
lemma exists_decomp (x : V) :
    ∃ (s : Finset (Fin 8 → ℕ)) (y : (Fin 8 → ℕ) → V),
      (∀ m ∈ s, y m ∈ Wm m) ∧ x = ∑ m ∈ s, y m := by
  classical
  have hx : x ∈ Submodule.span ℂ (Set.range (fun w : List (Fin 8) =>
      (Submodule.Quotient.mk (wordElt w) : V))) := by
    rw [span_mk_wordElt_eq_top]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  refine ⟨c.support.image (fun w => fun i => w.count i),
    fun m => ∑ w ∈ c.support.filter (fun w => (fun i => w.count i) = m),
      c w • (Submodule.Quotient.mk (wordElt w) : V), ?_, ?_⟩
  · intro m _
    refine Submodule.sum_mem _ fun w hw => ?_
    rw [Finset.mem_filter] at hw
    refine Submodule.smul_mem _ _ (Submodule.subset_span
      ⟨w, fun i => congrFun hw.2 i, rfl⟩)
  · have hfiber : ∑ m ∈ c.support.image (fun w => fun i => w.count i),
        (∑ w ∈ c.support.filter (fun w => (fun i => w.count i) = m),
          c w • (Submodule.Quotient.mk (wordElt w) : V))
        = ∑ w ∈ c.support, c w • (Submodule.Quotient.mk (wordElt w) : V) :=
      Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) _
    rw [hfiber]
    exact hc.symm

/-- The `λ`-weight space of `V` is one-dimensional, spanned by the highest weight vector. -/
lemma Wm_zero_eq :
    Wm (fun _ : Fin 8 => 0) = ℂ ∙ (Submodule.Quotient.mk (1 : FA (Fin 8)) : V) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro x ⟨w, hw, rfl⟩
    have hwnil : w = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr ?_
      intro a ha
      have h1 : 0 < w.count a := List.count_pos_iff.mpr ha
      rw [hw a] at h1
      exact Nat.lt_irrefl 0 h1
    subst hwnil
    rw [wordElt_nil]
    exact Submodule.mem_span_singleton_self _
  · refine Submodule.span_le.mpr ?_
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    refine Submodule.subset_span ⟨[], (fun i => by simp), ?_⟩
    rw [wordElt_nil]


lemma wt_injective : Function.Injective wt :=
  Submission.WeightIndependence.wtVec_injective

/-! ## The projection onto a single word space

For a finite set `s` of multiplicity vectors and a target `m₀ ∈ s` we build an endomorphism of `V`
which fixes `Wm m₀` and annihilates every `Wm m` with `m ∈ s`, `m ≠ m₀`: the product of the
"killers" `c • (Hbar j - (wt m j) • 1)` over `m ∈ s \ {m₀}`, where `j = j m` is a coordinate at
which `wt m` and `wt m₀` differ.  The construction is insensitive to the order of the product
because every killer acts on every `Wm n` by a scalar. -/

/-- The killer attached to `m` and a coordinate `j`: it annihilates a word vector of multiplicity
`m` and multiplies a word vector of multiplicity `m₀` by
`(wt m₀ j - wt m j)⁻¹ * (wt m₀ j - wt m j) = 1`. -/
def killer (m₀ m : Fin 8 → ℕ) (j : Fin 8) : Module.End ℂ V :=
  ((wt m₀ j - wt m j)⁻¹) • (Hbar E8 lam j - (wt m j) • (1 : Module.End ℂ V))

lemma killer_apply_mem_Wm (m₀ m n : Fin 8 → ℕ) (j : Fin 8) {x : V} (hx : x ∈ Wm n) :
    killer m₀ m j x = ((wt m₀ j - wt m j)⁻¹ * (wt n j - wt m j)) • x := by
  rw [killer, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, Hbar_apply_mem_Wm j hx]
  rw [← sub_smul, smul_smul]

lemma killer_mem {N : Submodule ℂ V} (hN : ∀ (i : Fin 8) {x : V}, x ∈ N → Hbar E8 lam i x ∈ N)
    (m₀ m : Fin 8 → ℕ) (j : Fin 8) {x : V} (hx : x ∈ N) : killer m₀ m j x ∈ N := by
  rw [killer, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  exact N.smul_mem _ (Submodule.sub_mem _ (hN j hx) (N.smul_mem _ hx))

/-- A product of killers along a list acts on `Wm n` by the product of the corresponding
scalars. -/
lemma prod_killer_apply (m₀ : Fin 8 → ℕ) (j : (Fin 8 → ℕ) → Fin 8) (l : List (Fin 8 → ℕ))
    (n : Fin 8 → ℕ) {x : V} (hx : x ∈ Wm n) :
    (l.map (fun m => killer m₀ m (j m))).prod x
      = (l.map (fun m => (wt m₀ (j m) - wt m (j m))⁻¹ * (wt n (j m) - wt m (j m)))).prod • x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
        map_smul, killer_apply_mem_Wm m₀ a n (j a) hx, smul_smul]
      congr 1
      ring

/-- A product of killers preserves every subspace stable under the `Hbar i`. -/
lemma prod_killer_mem (m₀ : Fin 8 → ℕ) (j : (Fin 8 → ℕ) → Fin 8) {N : Submodule ℂ V}
    (hN : ∀ (i : Fin 8) {x : V}, x ∈ N → Hbar E8 lam i x ∈ N)
    (l : List (Fin 8 → ℕ)) {x : V} (hx : x ∈ N) :
    (l.map (fun m => killer m₀ m (j m))).prod x ∈ N := by
  induction l with
  | nil => simpa using hx
  | cons a t ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply]
      exact killer_mem hN m₀ a (j a) ih

/-- **The killers project onto `Wm m₀`.**  If `x = ∑ m ∈ s, y m` with `y m ∈ Wm m` and `m₀ ∈ s`,
then the product of the killers over the elements of `s \ {m₀}` extracts `y m₀`. -/
lemma prod_killer_apply_sum (m₀ : Fin 8 → ℕ) (j : (Fin 8 → ℕ) → Fin 8) (s : Finset (Fin 8 → ℕ))
    (hm₀ : m₀ ∈ s) (hj : ∀ m ∈ s, m ≠ m₀ → wt m (j m) ≠ wt m₀ (j m))
    (y : (Fin 8 → ℕ) → V) (hy : ∀ m ∈ s, y m ∈ Wm m) :
    (((s.erase m₀).toList).map (fun m => killer m₀ m (j m))).prod (∑ m ∈ s, y m) = y m₀ := by
  classical
  set l : List (Fin 8 → ℕ) := (s.erase m₀).toList with hl
  have hmem : ∀ m ∈ s.erase m₀, m ∈ l := fun m hm => Finset.mem_toList.mpr hm
  have hzero : ∀ m ∈ s, m ≠ m₀ →
      ((l.map (fun m' => killer m₀ m' (j m'))).prod) (y m) = 0 := by
    intro m hm hne
    rw [prod_killer_apply m₀ j l m (hy m hm)]
    have hfac : ((wt m₀ (j m) - wt m (j m))⁻¹ * (wt m (j m) - wt m (j m))) = 0 := by
      rw [sub_self, mul_zero]
    have h0 : (0 : ℂ) ∈ l.map (fun m' =>
        (wt m₀ (j m') - wt m' (j m'))⁻¹ * (wt m (j m') - wt m' (j m'))) :=
      List.mem_map.mpr ⟨m, hmem m (Finset.mem_erase.mpr ⟨hne, hm⟩), hfac⟩
    rw [List.prod_eq_zero h0, zero_smul]
  rw [map_sum, Finset.sum_eq_single m₀ hzero (fun h => absurd hm₀ h)]
  rw [prod_killer_apply m₀ j l m₀ (hy m₀ hm₀)]
  have hone : (l.map (fun m =>
      (wt m₀ (j m) - wt m (j m))⁻¹ * (wt m₀ (j m) - wt m (j m)))).prod = 1 := by
    refine List.prod_eq_one fun z hz => ?_
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
    have hm' : m ∈ s.erase m₀ := Finset.mem_toList.mp hm
    have hne := hj m (Finset.mem_of_mem_erase hm') (Finset.ne_of_mem_erase hm')
    exact inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm)
  rw [hone, one_smul]

/-! ## The enveloping algebra module structure and the unique maximal submodule -/

/-- The enveloping algebra of `e₈`. -/
abbrev U : Type := UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ)

/-- `V` is a module over `U(e₈)` through `ρ = U.lift (act ω₁+ω₈)`. -/
noncomputable instance instModuleU : Module U V :=
  Module.compHom V (Submission.VermaNonzero.rho lam).toRingHom

noncomputable instance instIsScalarTower : IsScalarTower ℂ U V := by
  refine ⟨fun c u x => ?_⟩
  change Submission.VermaNonzero.rho lam (c • u) x
    = c • (Submission.VermaNonzero.rho lam u x)
  rw [map_smul, LinearMap.smul_apply]

/-- The highest weight vector of `V`. -/
abbrev v : V := Submodule.Quotient.mk (1 : FA (Fin 8))

lemma v_ne_zero : v ≠ 0 := Submission.VermaNonzero.mk_one_ne_zero

lemma v_mem_Wm_zero : v ∈ Wm (fun _ : Fin 8 => 0) := by
  refine Submodule.subset_span ⟨[], (fun i => by simp), ?_⟩
  rw [wordElt_nil]

/-- `Hbar i` maps any `U(e₈)`-submodule into itself. -/
lemma hbar_mem (N : Submodule U V) {x : V} (hx : x ∈ N) (i : Fin 8) :
    Hbar E8 lam i x ∈ N := by
  have h : (Submission.E8Weights.h i) • x = Hbar E8 lam i x := by
    rw [show Submission.E8Weights.h i
        = UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i) from rfl,
      ← Submission.VermaNonzero.rho_H lam i]
    rfl
  rw [← h]
  exact N.smul_mem' _ hx

lemma smul_mem_C (N : Submodule U V) (c : ℂ) {x : V} (hx : x ∈ N) : c • x ∈ N := by
  rw [← algebraMap_smul U c x]
  exact N.smul_mem _ hx

lemma hbar_mem' (N : Submodule U V) :
    ∀ (i : Fin 8) {x : V}, x ∈ N → Hbar E8 lam i x ∈ N :=
  fun i _ hx => hbar_mem N hx i

/-- **The weight components of an element of an `Hbar`-stable subspace lie in the subspace.** -/
theorem exists_decomp_mem (N : Submodule ℂ V)
    (hN : ∀ (i : Fin 8) {x : V}, x ∈ N → Hbar E8 lam i x ∈ N)
    {x : V} (hx : x ∈ N) :
    ∃ (s : Finset (Fin 8 → ℕ)) (y : (Fin 8 → ℕ) → V),
      (∀ m ∈ s, y m ∈ Wm m) ∧ (∀ m ∈ s, y m ∈ N) ∧ x = ∑ m ∈ s, y m := by
  classical
  obtain ⟨s, y, hy, hsum⟩ := exists_decomp x
  have key : ∀ m₀ ∈ s, y m₀ ∈ N := by
    intro m₀ hm₀
    have hjex : ∀ m : Fin 8 → ℕ, ∃ j : Fin 8, m = m₀ ∨ wt m j ≠ wt m₀ j := by
      intro m
      by_cases h : m = m₀
      · exact ⟨0, Or.inl h⟩
      · have hne : wt m ≠ wt m₀ := fun hh => h (wt_injective hh)
        obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
        exact ⟨j, Or.inr hj⟩
    choose j hj using hjex
    have hj' : ∀ m ∈ s, m ≠ m₀ → wt m (j m) ≠ wt m₀ (j m) :=
      fun m _ hne => (hj m).resolve_left hne
    have h1 := prod_killer_apply_sum m₀ j s hm₀ hj' y hy
    rw [← hsum] at h1
    have h2 := prod_killer_mem m₀ j hN (s.erase m₀).toList hx
    rw [h1] at h2
    exact h2
  exact ⟨s, y, hy, key, hsum⟩

/-- **The weight components of an element of a `U(e₈)`-submodule lie in the submodule.** -/
theorem exists_decomp_mem' (N : Submodule U V) {x : V} (hx : x ∈ N) :
    ∃ (s : Finset (Fin 8 → ℕ)) (y : (Fin 8 → ℕ) → V),
      (∀ m ∈ s, y m ∈ Wm m) ∧ (∀ m ∈ s, y m ∈ N) ∧ x = ∑ m ∈ s, y m := by
  have hstab : ∀ (i : Fin 8) {x : V},
      x ∈ N.restrictScalars ℂ → Hbar E8 lam i x ∈ N.restrictScalars ℂ :=
    fun i _ hx => (Submodule.restrictScalars_mem ℂ N _).mpr
      (hbar_mem N ((Submodule.restrictScalars_mem ℂ N _).mp hx) i)
  obtain ⟨s, y, hy, hmem, hsum⟩ := exists_decomp_mem (N.restrictScalars ℂ) hstab
    ((Submodule.restrictScalars_mem ℂ N x).mpr hx)
  exact ⟨s, y, hy, fun m hm => (Submodule.restrictScalars_mem ℂ N (y m)).mp (hmem m hm), hsum⟩

/-- A `U(e₈)`-submodule containing the highest weight vector is everything. -/
lemma eq_top_of_mem (N : Submodule U V) (h : v ∈ N) : N = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨u, hu⟩ := Submission.VermaNonzero.cyclic_V lam z
  have hz : z = u • v := by rw [← hu]; rfl
  rw [hz]
  exact N.smul_mem' u h

/-- **The sum of two proper submodules of `V` is proper.**  This reflects the fact that the
`λ`-weight space of the Verma module is one-dimensional, spanned by the highest weight vector. -/
theorem sup_ne_top (N₁ N₂ : Submodule U V) (h₁ : v ∉ N₁) (h₂ : v ∉ N₂) : v ∉ N₁ ⊔ N₂ := by
  classical
  intro hv
  obtain ⟨n₁, hn₁, n₂, hn₂, hsum12⟩ := Submodule.mem_sup.mp hv
  obtain ⟨s₁, y₁, hy₁, hm₁, hd₁⟩ := exists_decomp_mem' N₁ hn₁
  obtain ⟨s₂, y₂, hy₂, hm₂, hd₂⟩ := exists_decomp_mem' N₂ hn₂
  -- the combined weight decomposition of `v`
  set S : Finset (Fin 8 → ℕ) := insert 0 (s₁ ∪ s₂) with hSdef
  set Z : (Fin 8 → ℕ) → V := fun m =>
    (if m ∈ s₁ then y₁ m else 0) + (if m ∈ s₂ then y₂ m else 0) with hZdef
  have hsub₁ : s₁ ⊆ S := fun m hm => Finset.mem_insert_of_mem (Finset.mem_union_left _ hm)
  have hsub₂ : s₂ ⊆ S := fun m hm => Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)
  have hZmem : ∀ m ∈ S, Z m ∈ Wm m := by
    intro m _
    simp only [hZdef]
    by_cases h : m ∈ s₁
    · rw [if_pos h]
      by_cases h' : m ∈ s₂
      · rw [if_pos h']; exact Submodule.add_mem _ (hy₁ m h) (hy₂ m h')
      · rw [if_neg h']; simpa using hy₁ m h
    · rw [if_neg h]
      by_cases h' : m ∈ s₂
      · rw [if_pos h']; simpa using hy₂ m h'
      · rw [if_neg h']; simpa using (Submodule.zero_mem (Wm m) : (0 : V) ∈ Wm m)
  have hsumZ : (∑ m ∈ S, Z m) = v := by
    have heq : (∑ m ∈ S, Z m) = ∑ m ∈ S,
        ((if m ∈ s₁ then y₁ m else 0) + (if m ∈ s₂ then y₂ m else 0)) :=
      Finset.sum_congr rfl fun m _ => rfl
    rw [heq, Finset.sum_add_distrib]
    have h1 : (∑ m ∈ S, (if m ∈ s₁ then y₁ m else 0)) = ∑ m ∈ s₁, y₁ m := by
      refine (Finset.sum_subset (f := fun m => if m ∈ s₁ then y₁ m else 0) hsub₁
        (fun m _ hm => if_neg hm)).symm.trans ?_
      exact Finset.sum_congr rfl fun m hm => if_pos hm
    have h2 : (∑ m ∈ S, (if m ∈ s₂ then y₂ m else 0)) = ∑ m ∈ s₂, y₂ m := by
      refine (Finset.sum_subset (f := fun m => if m ∈ s₂ then y₂ m else 0) hsub₂
        (fun m _ hm => if_neg hm)).symm.trans ?_
      exact Finset.sum_congr rfl fun m hm => if_pos hm
    rw [h1, h2, ← hd₁, ← hd₂]
    exact hsum12
  -- the projector onto the `0`-weight space
  have hjex : ∀ m : Fin 8 → ℕ, ∃ j : Fin 8, m = 0 ∨ wt m j ≠ wt 0 j := by
    intro m
    by_cases h : m = 0
    · exact ⟨0, Or.inl h⟩
    · have hne : wt m ≠ wt 0 := fun hh => h (wt_injective hh)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      exact ⟨j, Or.inr hj⟩
  choose j hj using hjex
  have hj' : ∀ m ∈ S, m ≠ 0 → wt m (j m) ≠ wt 0 (j m) :=
    fun m _ hne => (hj m).resolve_left hne
  have h0S : (0 : Fin 8 → ℕ) ∈ S := Finset.mem_insert_self _ _
  have hPZ := prod_killer_apply_sum 0 j S h0S hj' Z hZmem
  rw [hsumZ] at hPZ
  have hPv : (((S.erase 0).toList).map (fun m => killer 0 m (j m))).prod v = v := by
    rw [prod_killer_apply 0 j (S.erase 0).toList 0 v_mem_Wm_zero]
    have hone : ((S.erase 0).toList.map (fun m =>
        (wt 0 (j m) - wt m (j m))⁻¹ * (wt 0 (j m) - wt m (j m)))).prod = 1 := by
      refine List.prod_eq_one fun z hz => ?_
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
      have hm' : m ∈ S.erase 0 := Finset.mem_toList.mp hm
      have hne := hj' m (Finset.mem_of_mem_erase hm') (Finset.ne_of_mem_erase hm')
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm)
    rw [hone, one_smul]
  -- the `0`-weight component of `v` is `v`, and it splits as `p₁ + p₂`
  set p₁ : V := (if (0 : Fin 8 → ℕ) ∈ s₁ then y₁ 0 else 0) with hp₁def
  set p₂ : V := (if (0 : Fin 8 → ℕ) ∈ s₂ then y₂ 0 else 0) with hp₂def
  have hZ0 : Z (0 : Fin 8 → ℕ) = v := by rw [← hPZ, hPv]
  have hsum_p : p₁ + p₂ = v := by
    rw [hp₁def, hp₂def]
    simp only [hZdef] at hZ0
    exact hZ0
  have hp₁N : p₁ ∈ N₁ := by
    by_cases h : (0 : Fin 8 → ℕ) ∈ s₁
    · rw [hp₁def, if_pos h]; exact hm₁ 0 h
    · rw [hp₁def, if_neg h]; exact N₁.zero_mem
  have hp₂N : p₂ ∈ N₂ := by
    by_cases h : (0 : Fin 8 → ℕ) ∈ s₂
    · rw [hp₂def, if_pos h]; exact hm₂ 0 h
    · rw [hp₂def, if_neg h]; exact N₂.zero_mem
  have hp₁W : p₁ ∈ Wm (fun _ : Fin 8 => 0) := by
    by_cases h : (0 : Fin 8 → ℕ) ∈ s₁
    · rw [hp₁def, if_pos h]; exact hy₁ 0 h
    · rw [hp₁def, if_neg h]; exact Submodule.zero_mem _
  have hp₂W : p₂ ∈ Wm (fun _ : Fin 8 => 0) := by
    by_cases h : (0 : Fin 8 → ℕ) ∈ s₂
    · rw [hp₂def, if_pos h]; exact hy₂ 0 h
    · rw [hp₂def, if_neg h]; exact Submodule.zero_mem _
  have hcore : v ∈ N₁ ∨ v ∈ N₂ := by
    by_cases hp1 : p₁ = 0
    · right
      have hp2v : p₂ = v := by rw [← hsum_p, hp1, zero_add]
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (by rw [← Wm_zero_eq]; exact hp₂W)
      have hne : c ≠ 0 := by
        intro h0
        have hp2 : p₂ = 0 := by rw [← hc, h0, zero_smul]
        rw [hp2v] at hp2
        exact v_ne_zero hp2
      have hv' : v = c⁻¹ • p₂ := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [hv']
      exact smul_mem_C N₂ c⁻¹ hp₂N
    · left
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
        (by rw [← Wm_zero_eq]; exact hp₁W)
      have hne : c ≠ 0 := by
        intro h0
        refine hp1 ?_
        rw [← hc, h0, zero_smul]
      have hv' : v = c⁻¹ • p₁ := by
        rw [← hc, smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [hv']
      exact smul_mem_C N₁ c⁻¹ hp₁N
  rcases hcore with hc | hc
  · exact h₁ (eq_top_of_mem N₁ hc ▸ Submodule.mem_top)
  · exact h₂ (eq_top_of_mem N₂ hc ▸ Submodule.mem_top)



/-! ## The highest weight vector of the simple quotient

The quotient `V ⧸ N` inherits the highest weight vector `vbar N` (`≠ 0` when `v ∉ N`).  The
remaining structural facts about the action of `e₈` on the quotient (that `vbar` is a highest
weight vector and generates the quotient) are stated here in the least ambiguous form; see the
note in the roadmap: the `SMul U (V ⧸ N)` and `LieRingModule e₈ (V ⧸ N)` instances on the quotient
are not automatically the quotient ones, so statements mentioning them explicitly are delicate. -/

/-- The image of the highest weight vector in the quotient `V ⧸ N`. -/
def vbar (N : Submodule U V) : V ⧸ N := Submodule.Quotient.mk v

lemma vbar_ne_zero (N : Submodule U V) (hv : v ∉ N) : vbar N ≠ 0 := by
  intro h
  exact hv ((Submodule.Quotient.mk_eq_zero N).mp h)

/-! ## The unique maximal submodule and the simple quotient `L(ω₁+ω₈)` -/

/-- The canonical `U(e₈)`-module structure on a quotient of `V` by a `U(e₈)`-submodule.  This is
declared with high priority so that it is not confused with the module structure obtained from the
Lie-module dictionary. -/
noncomputable instance instModuleUQuot (N : Submodule U V) : Module U (V ⧸ N) :=
  Submodule.Quotient.module N

/-- The quotient `V ⧸ N` inherits the `ℂ`-module structure compatibly with the `U(e₈)`-action. -/
noncomputable instance instIsScalarTowerQuot (N : Submodule U V) : IsScalarTower ℂ U (V ⧸ N) := by
  refine ⟨fun c u x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | _ m =>
      rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
        IsScalarTower.smul_assoc]

/-- **`V` has a maximal proper submodule**, i.e. a largest submodule not containing the highest
weight vector.  (Uniqueness of the maximal submodule of the Verma module.) -/
theorem exists_max_submodule :
    ∃ N : Submodule U V, v ∉ N ∧ ∀ N' : Submodule U V, v ∉ N' → N' ≤ N :=
  Commons.Algebra.Module.exists_max_submodule_notMem v
    (fun N₁ N₂ h₁ h₂ => sup_ne_top N₁ N₂ h₁ h₂) v_ne_zero

/-- A maximal proper submodule of `V` is a coatom in the lattice of submodules. -/
theorem isCoatom_of_max {N : Submodule U V}
    (hv : v ∉ N) (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) : IsCoatom N := by
  refine ⟨fun htop => hv (htop ▸ Submodule.mem_top), ?_⟩
  intro N' hlt
  by_contra hne
  have hv' : v ∉ N' := fun hvv => hne (eq_top_of_mem N' hvv)
  exact (lt_iff_le_not_ge.mp hlt).2 (hmax N' hv')

/-- **The quotient of the Verma module by its maximal submodule is simple.** -/
theorem quotient_isSimpleModule {N : Submodule U V} (hv : v ∉ N)
    (hmax : ∀ N' : Submodule U V, v ∉ N' → N' ≤ N) :
    @IsSimpleModule U _ (V ⧸ N) (Submodule.Quotient.addCommGroup N)
      (Submodule.Quotient.module N) :=
  isSimpleModule_iff_isCoatom.mpr (isCoatom_of_max hv hmax)

/-- **Existence of a nonzero irreducible `e₈`-module of highest weight `ω₁ + ω₈`.** -/
theorem exists_irreducible_highest_weight :
    ∃ (L : Type) (_ : AddCommGroup L) (_ : Module ℂ L)
      (_ : LieRingModule (LieAlgebra.e₈ ℂ) L) (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) L),
      Nontrivial L ∧ LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) L := by
  obtain ⟨N, hv, hmax⟩ := exists_max_submodule
  have hsimple : @IsSimpleModule U _ (V ⧸ N) (Submodule.Quotient.addCommGroup N)
      (Submodule.Quotient.module N) := quotient_isSimpleModule hv hmax
  refine ⟨V ⧸ N, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact ⟨⟨Submodule.Quotient.mk v, 0,
      fun h => hv ((Submodule.Quotient.mk_eq_zero N).mp h)⟩⟩
  · rw [Commons.RepresentationTheory.LieEnveloping.isIrreducible_iff_isSimpleModule
      (M := V ⧸ N) (fun x m => rfl)]
    exact hsimple

end Submission.VermaWeight

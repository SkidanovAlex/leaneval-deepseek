import Submission.ZagierHoffmanProof.CountT0
import Submission.ZagierHoffmanProof.ATBridge2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# The `t`-motive datum of the MZV application (Dac §5.3)

For the MZV form of Theorems B/D one runs `LinearIndependence.linear_independence` on the
`Finset` `S` of weight-`w` tuples of `𝒯0` (entries `< q`, i.e. `≤ q`) with unit `Q`'s.  This file
builds that datum:

* `tupleList 𝔰` — the `List (ℕ × Polynomial (Ambient F))` of a `Fin`-indexed tuple `𝔰`, all `Q = 1`;
* `T0list w hw v` — the list attached to a value `v ∈ 𝒯0 F w`: the chosen bounded representative
  `T0tuple`, **reversed** so that `(T0list).get (Fin.rev j)` recovers the tuple in its natural order
  (this is the order the bridge `ATBridge2.bridge` expects);
* `T0exp w hw v : Fin (T0list).length → ℕ+` — the exponent tuple in that order, with the five
  matching properties (`T0list_ne_nil`, `T0list_get_two`, `T0list_get_pos`, `T0exp_le`,
  `T0exp_zeta`) required by `ATBridge2.f_empty_vanishing` / `ATBridge2.bridge`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## §1. The list of a tuple of exponents -/

/-- The `List (ℕ × Polynomial (Ambient F))` attached to a `Fin`-indexed tuple of positive
exponents, all `Q`'s being `1` (Dac's `𝒯0`-datum). -/
@[reducible] noncomputable def tupleList {n : ℕ} (𝔰 : Fin n → ℕ+) :
    List (ℕ × PowerSeries (Ambient F)) :=
  List.ofFn (fun j : Fin n => ((𝔰 j : ℕ), (1 : PowerSeries (Ambient F))))

lemma tupleList_length {n : ℕ} (𝔰 : Fin n → ℕ+) : (tupleList F 𝔰).length = n :=
  List.length_ofFn

lemma tupleList_get {n : ℕ} (𝔰 : Fin n → ℕ+) (j : Fin (tupleList F 𝔰).length) :
    (tupleList F 𝔰).get j
      = (((𝔰 (Fin.cast (tupleList_length F 𝔰) j)) : ℕ), (1 : PowerSeries (Ambient F))) := by
  rw [List.get_ofFn]

/-- `Fin.rev` of a `Fin.cast` of a `Fin.rev` is the identity (up to the `cast`). -/
lemma rev_cast_rev {m n : ℕ} (hl : m = n) (j : Fin m) :
    Fin.rev (Fin.cast hl (Fin.rev j)) = ⟨j.val, by omega⟩ := by
  refine Fin.ext ?_
  simp only [Fin.val_rev, Fin.val_cast]
  omega

/-! ## §2. The datum of a value of `𝒯0 F w` -/

/-- The `t`-motive list of a value of `𝒯0 F w`: the tuple of the chosen bounded representative,
**reversed** so that `List.get · (Fin.rev j)` recovers the tuple in its natural order. -/
@[reducible] noncomputable def T0list (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    List (ℕ × PowerSeries (Ambient F)) :=
  tupleList F (fun i : Fin (T0tuple F w hw v).1 => (T0tuple F w hw v).2 (Fin.rev i))

lemma T0list_eq (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    T0list F w hw v = tupleList F
      (fun i : Fin (T0tuple F w hw v).1 => (T0tuple F w hw v).2 (Fin.rev i)) := rfl

lemma T0list_length (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    (T0list F w hw v).length = (T0tuple F w hw v).1 :=
  tupleList_length F _

lemma T0list_ne_nil (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : T0list F w hw v ≠ [] := by
  intro h
  have h1 := T0list_length F w hw v
  have h2 := T0tuple_arity_pos F w hw v
  rw [h] at h1
  simp at h1
  omega

lemma T0list_get_two (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (j : Fin (T0list F w hw v).length) : ((T0list F w hw v).get j).2 = 1 := by
  simp only [T0list]
  rw [tupleList_get]

lemma T0list_get_pos (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (j : Fin (T0list F w hw v).length) : 1 ≤ ((T0list F w hw v).get j).1 := by
  simp only [T0list]
  rw [tupleList_get]
  exact ((T0tuple F w hw v).2 _).2

/-- The exponent tuple of `T0list`, in the order required by the bridge (so that
`(T0exp v j : ℕ) = ((T0list v).get (Fin.rev j)).1`). -/
noncomputable def T0exp (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    Fin (T0list F w hw v).length → ℕ+ :=
  fun j => ⟨((T0list F w hw v).get (Fin.rev j)).1, by
    have h := T0list_get_pos F w hw v (Fin.rev j)
    omega⟩

@[simp] lemma T0exp_apply (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (j : Fin (T0list F w hw v).length) :
    (T0exp F w hw v j : ℕ) = ((T0list F w hw v).get (Fin.rev j)).1 := rfl

lemma T0exp_val (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (j : Fin (T0list F w hw v).length) :
    (T0exp F w hw v j : ℕ) = ((T0tuple F w hw v).2
      ⟨j.val, by simpa [T0list_length F w hw v] using j.isLt⟩ : ℕ) := by
  rw [T0exp_apply]
  simp only [T0list]
  rw [tupleList_get]
  congr 1
  exact congrArg (fun k : Fin (T0tuple F w hw v).1 => ((T0tuple F w hw v).2 k : ℕ))
    (rev_cast_rev (T0list_length F w hw v) j)

lemma T0exp_le (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w})
    (j : Fin (T0list F w hw v).length) : (T0exp F w hw v j : ℕ) ≤ Nat.card F := by
  have h := T0tuple_lt F w hw v ⟨j.val, by
    simpa [T0list_length F w hw v] using j.isLt⟩
  rw [T0exp_val F w hw v j]
  exact le_of_lt h

/-- **The MZV value of the datum**: `ζ_A` of the exponent tuple of `v` is `v` itself. -/
lemma T0exp_zeta (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ζ_A F (T0exp F w hw v) = v.val := by
  refine (ζ_A_eq_of_reindex F (T0list_length F w hw v) _ _ (fun i => Subtype.ext ?_)).trans
    (T0tuple_zeta F w hw v)
  exact T0exp_val F w hw v i

/-! ## §3. The weight and the `(LD)` input of the MZV application -/

lemma T0exp_weight (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    (∑ j : Fin (T0list F w hw v).length, (T0exp F w hw v j : ℕ)) = w := by
  have h1 : ∀ j : Fin (T0list F w hw v).length,
      (T0exp F w hw v j : ℕ) = ((T0tuple F w hw v).2
        (Fin.cast (T0list_length F w hw v) j) : ℕ) := by
    intro j
    rw [T0exp_val F w hw v j]
    exact congrArg (fun k : Fin (T0tuple F w hw v).1 => ((T0tuple F w hw v).2 k : ℕ))
      (Fin.ext rfl)
  rw [Finset.sum_congr rfl (fun j _ => h1 j)]
  exact (Fintype.sum_equiv (Fin.castOrderIso (T0list_length F w hw v)).toEquiv
      (fun j : Fin (T0list F w hw v).length =>
        ((T0tuple F w hw v).2 (Fin.cast (T0list_length F w hw v) j) : ℕ))
      (fun i : Fin (T0tuple F w hw v).1 => ((T0tuple F w hw v).2 i : ℕ))
      (fun j => by simp [Fin.castOrderIso_apply])).trans (T0tuple_weight F w hw v)

/-- `𝒯0 F w` is finite as a subtype of `CompletionAtInfty F` (`Fintype` form). -/
lemma finiteT0 (w : ℕ) (hw : 1 ≤ w) :
    Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} :=
  Finite.of_injective (valueToShape0 F w hw) (valueToShape0_inj F w hw)

/-- **The `(LD)` input of the MZV application** (`a = 0`): a `K`-linear relation among the MZV's of
`𝒯0 F w` (all of the same weight `w`, entries `≤ q`, unit `Q`'s) forces the corresponding
`L`-series relation to vanish.  This is `f_∅(θ) = 0`. -/
theorem T0_f_empty_vanishing (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (c : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → RatFunc F)
    (h : ∑ v : {x // x ∈ 𝒯0 F w}, c v • v.val = 0) :
    ∑ v : {x // x ∈ 𝒯0 F w}, ambKHomAmb F (c v) * evalSeriesGen
        (atLrGen (Nat.card F) (ambOmega F) (T0list F w hw v)) (ambTheta F) = 0 := by
  refine f_empty_vanishing F (T0list F w hw) (fun v => T0list_ne_nil F w hw v)
    (fun v j => T0list_get_two F w hw v j) (fun v j => T0list_get_pos F w hw v j)
    (T0exp F w hw) (fun v j => T0exp_apply F w hw v j) (fun v j => T0exp_le F w hw v j)
    w (fun v => T0exp_weight F w hw v) c ?_
  refine (Finset.sum_congr rfl (fun v _ => ?_)).trans h
  rw [T0exp_zeta F w hw v]

/-! ## §4. The `Finset` `S` of tuples and the coefficient function `cf` -/

attribute [local instance 100] Classical.decEq

/-- The `List (ℕ × Polynomial (Ambient F))` version (`tmF`'s index type). -/
@[reducible] noncomputable def tupleListP {n : ℕ} (𝔰 : Fin n → ℕ+) :
    List (ℕ × Polynomial (Ambient F)) :=
  List.ofFn (fun j : Fin n => ((𝔰 j : ℕ), (1 : Polynomial (Ambient F))))

lemma tupleListP_length {n : ℕ} (𝔰 : Fin n → ℕ+) : (tupleListP F 𝔰).length = n :=
  List.length_ofFn

lemma tupleListP_get {n : ℕ} (𝔰 : Fin n → ℕ+) (j : Fin (tupleListP F 𝔰).length) :
    (tupleListP F 𝔰).get j
      = (((𝔰 (Fin.cast (tupleListP_length F 𝔰) j)) : ℕ), (1 : Polynomial (Ambient F))) := by
  rw [List.get_ofFn]

/-- The polynomial and power-series forms of the tuple list agree under `tmCoe`. -/
lemma tmCoe_tupleListP {n : ℕ} (𝔰 : Fin n → ℕ+) :
    tmCoe (K := Ambient F) (tupleListP F 𝔰) = tupleList F 𝔰 := by
  simp only [tupleListP, tupleList, tmCoe, List.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_apply, Polynomial.coe_one]

/-- **The `Finset` `S` of the MZV application**: the weight-`w` `𝒯0`-tuples as lists. -/
noncomputable def T0S (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}] :
    Finset (List (ℕ × Polynomial (Ambient F))) :=
  Finset.univ.image (fun v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} =>
    tupleListP F (T0exp F w hw v))

lemma mem_T0S {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} :
    s ∈ T0S F w hw ↔ ∃ v, tupleListP F (T0exp F w hw v) = s := by
  simp only [T0S, Finset.mem_image, Finset.mem_univ, true_and]

lemma T0S_ne_nil {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) : s ≠ [] := by
  obtain ⟨v, rfl⟩ := (mem_T0S F).mp hs
  intro hnil
  have h1 : (tupleListP F (T0exp F w hw v)).length = 0 := by rw [hnil]; rfl
  rw [tupleListP_length F (T0exp F w hw v), T0list_length F w hw v] at h1
  have h2 := T0tuple_arity_pos F w hw v
  omega

lemma T0S_get_two {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw)
    (j : Fin s.length) : (s.get j).2 = 1 := by
  obtain ⟨v, rfl⟩ := (mem_T0S F).mp hs
  rw [tupleListP_get]

lemma T0S_get_pos {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw)
    (j : Fin s.length) : 1 ≤ (s.get j).1 := by
  obtain ⟨v, rfl⟩ := (mem_T0S F).mp hs
  rw [tupleListP_get]
  exact (T0exp F w hw v _).2

lemma T0S_weight {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) :
    tmWeight s = w := by
  obtain ⟨v, rfl⟩ := (mem_T0S F).mp hs
  rw [tmWeight, tupleListP, List.map_ofFn, List.sum_ofFn]
  exact T0exp_weight F w hw v

/-- **The coefficient function `cf` of the MZV application**: the coefficient attached to a tuple
(`0` off the image). -/
noncomputable def T0cf (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F)) :
    List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F) :=
  fun t => if h : ∃ v, tupleListP F (T0exp F w hw v) = t then
    b (Classical.choose h) else 0

/-! ## §5. Injectivity of `v ↦ tupleListP (T0exp v)` and `T0cf_apply` -/

attribute [local instance 100] Classical.decEq

lemma tupleListP_getElem? {n : ℕ} (𝔰 : Fin n → ℕ+) (k : ℕ) :
    (tupleListP F 𝔰)[k]? = if h : k < n then
      some (((𝔰 ⟨k, h⟩ : ℕ), (1 : Polynomial (Ambient F)))) else none := by
  rw [tupleListP, List.getElem?_ofFn]

/-- `tupleListP` is injective at a fixed arity. -/
lemma tupleListP_inj {n : ℕ} {𝔰 𝔰' : Fin n → ℕ+}
    (h : tupleListP F 𝔰 = tupleListP F 𝔰') : 𝔰 = 𝔰' := by
  have hmap : (List.ofFn fun j : Fin n => (𝔰 j : ℕ))
      = List.ofFn fun j : Fin n => (𝔰' j : ℕ) := by
    have hh := congrArg (List.map Prod.fst) h
    simp only [tupleListP, List.map_ofFn] at hh
    have h2 : (fun j : Fin n => (𝔰 j : ℕ))
        = (Prod.fst ∘ fun j : Fin n => ((𝔰 j : ℕ), (1 : Polynomial (Ambient F)))) := rfl
    have h3 : (fun j : Fin n => (𝔰' j : ℕ))
        = (Prod.fst ∘ fun j : Fin n => ((𝔰' j : ℕ), (1 : Polynomial (Ambient F)))) := rfl
    rw [h2, h3]
    exact hh
  funext i
  have h1 := congrArg (fun l : List ℕ => l[i.val]?) hmap
  rw [List.getElem?_ofFn, dif_pos i.isLt, List.getElem?_ofFn, dif_pos i.isLt] at h1
  exact Subtype.ext (Option.some.inj h1)

/-- **Injectivity of the tuple attached to a value of `𝒯0 F w`**. -/
lemma T0exp_listP_injective {w : ℕ} (hw : 1 ≤ w)
    {v v' : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}}
    (h : tupleListP F (T0exp F w hw v) = tupleListP F (T0exp F w hw v')) : v = v' := by
  have hlen : (T0list F w hw v).length = (T0list F w hw v').length := by
    rw [← tupleListP_length F (T0exp F w hw v), h, tupleListP_length F (T0exp F w hw v')]
  have hζ : ζ_A F (T0exp F w hw v) = ζ_A F (T0exp F w hw v') := by
    refine ζ_A_eq_of_reindex F hlen _ _ (fun i => Subtype.ext ?_)
    have h1 := congrArg
      (fun l : List (ℕ × Polynomial (Ambient F)) => (l[i.val]?).map Prod.fst) h
    rw [tupleListP_getElem?, tupleListP_getElem?, dif_pos i.isLt,
      dif_pos (by rw [← hlen]; exact i.isLt)] at h1
    simp only [Option.map_some] at h1
    have h3 : Option.some (T0exp F w hw v i : ℕ)
        = Option.some (T0exp F w hw v' ⟨i.val, by rw [← hlen]; exact i.isLt⟩ : ℕ) := h1
    exact Option.some.inj h3
  rw [T0exp_zeta F w hw v, T0exp_zeta F w hw v'] at hζ
  exact Subtype.ext hζ

/-- **`T0cf` recovers the coefficient**: on a tuple coming from `v`, the coefficient function
returns `b v`. -/
lemma T0cf_apply {w : ℕ} (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    T0cf F w hw b (tupleListP F (T0exp F w hw v)) = b v := by
  rw [T0cf, dif_pos (show ∃ u, tupleListP F (T0exp F w hw u)
    = tupleListP F (T0exp F w hw v) from ⟨v, rfl⟩)]
  congr 1
  exact T0exp_listP_injective F hw (Classical.choose_spec
    (show ∃ u, tupleListP F (T0exp F w hw u) = tupleListP F (T0exp F w hw v) from ⟨v, rfl⟩))

end ZagierHoffmanPositiveChar




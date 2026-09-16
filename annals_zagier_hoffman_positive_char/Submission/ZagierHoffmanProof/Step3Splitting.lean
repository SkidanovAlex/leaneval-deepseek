import Submission.ZagierHoffmanProof.MZVDatum
import Submission.Commons.Combinatorics.List.take_eq_take_imp_eq_of_sup_lt

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset
open scoped WithZero Topology

/-!
# Dac §5.3 Step 3: the `tmF`-splitting in situ

`ATBridge2.evalSeriesGen_tmF_single` collapses `tmF` to a single summand whenever the prefix `t` is
"uniquely extendable".  Here we instantiate it for the MZV datum `MZVDatum.T0S` / `T0cf`; the
`m_i`-combinatorics is supplied by the commons lemma
`Commons.Combinatorics.List.take_eq_take_imp_eq_of_sup_lt` (with the `m₀`-bound
`((T0S.filter (· ≠ s₀)).sup (fun s => ((s.zip s₀).takeWhile (fun p => p.1 = p.2)).length) < k`).

The resulting identity

  `f_𝔱(θ) = b_v(θ)·𝓛(𝔰_v \ 𝔱)(θ)`

is the second relation of Step 3 (`(II)`); combined with `ATBridge2.bridge_mul` on the dropped
suffix it gives `π̃^{w-w(𝔱)}·f_𝔱(θ) = b_v(θ)·ambInfHom (ζ_A 𝔰_suffix)`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

attribute [local instance 100] Classical.decEq

/-- The dropped tail of an element of `T0S` is again a unit-`Q` list with exponents `≥ 1`. -/
lemma T0S_drop_mem_two {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) (k : ℕ) :
    ∀ x ∈ s.drop k, x.2 = 1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact T0S_get_two F hs j

lemma T0S_drop_mem_pos {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) (k : ℕ) :
    ∀ x ∈ s.drop k, 1 ≤ x.1 := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact T0S_get_pos F hs j

/-- **The weight of the dropped tail**: `w - tmWeight (s.take k)`. -/
lemma T0S_drop_weight {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) (k : ℕ) :
    tmWeight (s.drop k) + tmWeight (s.take k) = w := by
  have h1 := tmWeight_take_add_drop s k
  have h2 := T0S_weight F hs
  omega

/-- `GSuperEntire` of the `L`-series of the dropped tail. -/
lemma gSuperEntire_tmL_T0drop {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) (k : ℕ) :
    GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F) (s.drop k)) :=
  gSuperEntire_tmL_unit F (s.drop k) (T0S_drop_mem_two F hs k) (T0S_drop_mem_pos F hs k)

/-- The prefix `t = s₀.take k` of a `𝒯0`-tuple is uniquely extendable among the elements of `T0S`
as soon as `k` exceeds the maximal common-prefix length with the other elements. -/
theorem T0S_unique_take (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hk : ((T0S F w hw).filter (fun s => s ≠ tupleListP F (T0exp F w hw v))).sup
      (fun s => ((s.zip (tupleListP F (T0exp F w hw v))).takeWhile
        (fun p => p.1 = p.2)).length) < k)
    (hklen : k ≤ (tupleListP F (T0exp F w hw v)).length) :
    ∀ s ∈ T0S F w hw,
      s.take ((tupleListP F (T0exp F w hw v)).take k).length
        = (tupleListP F (T0exp F w hw v)).take k
      → s = tupleListP F (T0exp F w hw v) := by
  have hlen : ((tupleListP F (T0exp F w hw v)).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hklen]
  intro s hs hst
  refine Commons.Combinatorics.List.take_eq_take_imp_eq_of_sup_lt
    (k := ((tupleListP F (T0exp F w hw v)).take k).length)
    (T0S F w hw) (tupleListP F (T0exp F w hw v)) ?_ hs ?_
  · rw [hlen]
    exact hk
  · rw [hst, hlen]

/-- **Step 3 (II) in situ**: for the MZV datum, `f_𝔱(θ)` is the single term
`b_v(θ)·𝓛(𝔰_v \ 𝔱)(θ)`. -/
theorem evalSeriesGen_tmF_T0 (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hk : ((T0S F w hw).filter (fun s => s ≠ tupleListP F (T0exp F w hw v))).sup
      (fun s => ((s.zip (tupleListP F (T0exp F w hw v))).takeWhile
        (fun p => p.1 = p.2)).length) < k)
    (hklen : k ≤ (tupleListP F (T0exp F w hw v)).length)
    (hse : GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F)
      ((tupleListP F (T0exp F w hw v)).drop k))) :
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
        ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F)
      = (b v).eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
          ((tupleListP F (T0exp F w hw v)).drop k)) (ambTheta F) := by
  have hlen : ((tupleListP F (T0exp F w hw v)).take k).length = k := by
    rw [List.length_take, Nat.min_eq_left hklen]
  have htake : (tupleListP F (T0exp F w hw v)).take
      ((tupleListP F (T0exp F w hw v)).take k).length
      = (tupleListP F (T0exp F w hw v)).take k := by
    rw [hlen]
  have hse' : GSuperEntire ambGamma (tmL (Nat.card F) (ambOmega F)
      ((tupleListP F (T0exp F w hw v)).drop
        ((tupleListP F (T0exp F w hw v)).take k).length)) := by
    rw [hlen]
    exact hse
  have h1 := evalSeriesGen_tmF_single (F := F) w
    (S := T0S F w hw) (cf := T0cf F w hw b)
    (t := (tupleListP F (T0exp F w hw v)).take k)
    (s₀ := tupleListP F (T0exp F w hw v))
    (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) htake
    (T0S_unique_take F w hw v hk hklen) hse'
  rw [h1, hlen, T0cf_apply F hw b v]

/-- **Step 3 (II) in situ, with the `GSuperEntire` side condition discharged.** -/
theorem evalSeriesGen_tmF_T0' (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hk : ((T0S F w hw).filter (fun s => s ≠ tupleListP F (T0exp F w hw v))).sup
      (fun s => ((s.zip (tupleListP F (T0exp F w hw v))).takeWhile
        (fun p => p.1 = p.2)).length) < k)
    (hklen : k ≤ (tupleListP F (T0exp F w hw v)).length) :
    evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
        ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F)
      = (b v).eval (ambTheta F) * evalSeriesGen (tmL (Nat.card F) (ambOmega F)
          ((tupleListP F (T0exp F w hw v)).drop k)) (ambTheta F) :=
  evalSeriesGen_tmF_T0 F w hw b v hk hklen
    (gSuperEntire_tmL_T0drop F
      (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k)

/-! ## §3. The suffix datum and the bridge on the dropped tail -/

attribute [local instance 100] Classical.decEq

/-- The `PowerSeries` list underlying the `L`-series of `L` (`tmL q ω L = atLrGen q ω …`). -/
@[reducible] noncomputable def suffixList (L : List (ℕ × Polynomial (Ambient F))) :
    List (ℕ × PowerSeries (Ambient F)) :=
  (tmCoe (K := Ambient F) L).reverse

lemma tmL_eq_atLrGen_suffixList {q : ℕ} [FrobPow (Ambient F) q] (ω : PowerSeries (Ambient F))
    (L : List (ℕ × Polynomial (Ambient F))) :
    tmL q ω L = atLrGen q ω (suffixList F L) := rfl

lemma mem_suffixList {x : ℕ × PowerSeries (Ambient F)}
    {L : List (ℕ × Polynomial (Ambient F))} :
    x ∈ suffixList F L ↔ ∃ y ∈ L, (y.1, (y.2 : PowerSeries (Ambient F))) = x := by
  simp only [suffixList, List.mem_reverse, tmCoe, List.mem_map]

lemma suffixList_ne_nil {L : List (ℕ × Polynomial (Ambient F))} (hL : L ≠ []) :
    suffixList F L ≠ [] := by
  simp only [suffixList, List.reverse_eq_nil_iff, ne_eq]
  intro h
  exact hL (List.eq_nil_of_length_eq_zero (by
    have h2 : (tmCoe (K := Ambient F) L).length = 0 := by rw [h]; rfl
    simp only [tmCoe, List.length_map] at h2
    exact h2))

lemma suffixList_mem_two {L : List (ℕ × Polynomial (Ambient F))}
    (hL : ∀ x ∈ L, x.2 = 1) : ∀ x ∈ suffixList F L, x.2 = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_suffixList F).mp hx
  simp only [hL y hy, Polynomial.coe_one]

lemma suffixList_mem_pos {L : List (ℕ × Polynomial (Ambient F))}
    (hL : ∀ x ∈ L, 1 ≤ x.1) : ∀ x ∈ suffixList F L, 1 ≤ x.1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_suffixList F).mp hx
  exact hL y hy

lemma suffixList_mem_le {L : List (ℕ × Polynomial (Ambient F))}
    (hL : ∀ x ∈ L, x.1 ≤ Nat.card F) : ∀ x ∈ suffixList F L, x.1 ≤ Nat.card F := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_suffixList F).mp hx
  exact hL y hy

/-- The exponent family of the suffix, in the order required by the bridge. -/
noncomputable def suffixExp (L : List (ℕ × Polynomial (Ambient F)))
    (hL : ∀ x ∈ L, 1 ≤ x.1) : Fin (suffixList F L).length → ℕ+ :=
  fun j => ⟨((suffixList F L).get (Fin.rev j)).1, by
    have h := suffixList_mem_pos F hL _ (List.get_mem (suffixList F L) (Fin.rev j))
    omega⟩

@[simp] lemma suffixExp_apply (L : List (ℕ × Polynomial (Ambient F)))
    (hL : ∀ x ∈ L, 1 ≤ x.1) (j : Fin (suffixList F L).length) :
    (suffixExp F L hL j : ℕ) = ((suffixList F L).get (Fin.rev j)).1 := rfl

lemma tupleListP_get_le {n : ℕ} (𝔰 : Fin n → ℕ+)
    (h : ∀ i, (𝔰 i : ℕ) ≤ Nat.card F) (j : Fin (tupleListP F 𝔰).length) :
    ((tupleListP F 𝔰).get j).1 ≤ Nat.card F := by
  rw [tupleListP_get]
  exact h _

lemma T0S_get_le {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw)
    (j : Fin s.length) : (s.get j).1 ≤ Nat.card F := by
  obtain ⟨v, rfl⟩ := (mem_T0S F).mp hs
  exact tupleListP_get_le F (T0exp F w hw v) (T0exp_le F w hw v) j

lemma T0S_drop_mem_le {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) (k : ℕ) :
    ∀ x ∈ s.drop k, x.1 ≤ Nat.card F := by
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_of_mem_drop hx)
  exact T0S_get_le F hs j

lemma drop_ne_nil_of_lt_length {α : Type*} {L : List α} {k : ℕ} (h : k < L.length) :
    L.drop k ≠ [] := by
  intro hnil
  have h1 : (L.drop k).length = 0 := by rw [hnil]; rfl
  rw [List.length_drop] at h1
  omega

/-! ## §4. The bridge on the dropped tail -/

/-- **Step 3 (II) completed**: the `L`-series of the dropped tail satisfies the bridge, i.e.
`π̃^{w(suffix)}·𝓛(suffix)(θ) = b_v(θ)·ambInfHom (ζ_A 𝔰_suffix)`. -/
theorem bridge_T0drop (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hkl : k < (tupleListP F (T0exp F w hw v)).length) :
    (ambPiTilde F) ^ (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
          (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k) j : ℕ))
      * ((b v).eval (ambTheta F) * evalSeriesGen
          (tmL (Nat.card F) (ambOmega F) ((tupleListP F (T0exp F w hw v)).drop k))
          (ambTheta F))
      = (b v).eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
            (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k))) := by
  have hs : tupleListP F (T0exp F w hw v) ∈ T0S F w hw :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have hLpos : ∀ x ∈ (tupleListP F (T0exp F w hw v)).drop k, 1 ≤ x.1 :=
    T0S_drop_mem_pos F hs k
  have h1 := bridge_mul F (suffixList F ((tupleListP F (T0exp F w hw v)).drop k))
    (suffixList_ne_nil F (drop_ne_nil_of_lt_length hkl))
    (fun j => suffixList_mem_two F (T0S_drop_mem_two F hs k)
      _ (List.get_mem (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)) j))
    (fun j => suffixList_mem_pos F hLpos _
      (List.get_mem (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)) j))
    (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k) hLpos)
    (fun j => rfl)
    (fun j => suffixList_mem_le F (T0S_drop_mem_le F hs k)
      _ (List.get_mem (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)) (Fin.rev j)))
    (b v)
  exact h1

/-- ★★★ **Step 3 (II), complete**: the second relation of Dac §5.3,
`π̃^{w(𝔰_v ⧵ 𝔱)}·f_𝔱(θ) = b_v(θ)·ambInfHom (ζ_A 𝔰_suffix)`. -/
theorem step3_II_T0 (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hk : ((T0S F w hw).filter (fun s => s ≠ tupleListP F (T0exp F w hw v))).sup
      (fun s => ((s.zip (tupleListP F (T0exp F w hw v))).takeWhile
        (fun p => p.1 = p.2)).length) < k)
    (hkl : k < (tupleListP F (T0exp F w hw v)).length) :
    (ambPiTilde F) ^ (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
          (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k) j : ℕ))
      * evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
          ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F)
      = (b v).eval (ambTheta F) * ambInfHom F (ζ_A F
          (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
            (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k))) := by
  rw [evalSeriesGen_tmF_T0' F w hw b v hk (le_of_lt hkl)]
  exact bridge_T0drop F w hw b v hkl

/-! ## §5. The expoent sum of the suffix is the weight of the dropped tail -/

/-- The weight of a list of pairs with `ℕ` first components. -/
def listWeight {α : Type*} (t : List (ℕ × α)) : ℕ := (t.map Prod.fst).sum

lemma listWeight_rev_get {α : Type*} (M : List (ℕ × α)) :
    (∑ j : Fin M.reverse.length, ((M.reverse).get (Fin.rev j)).1) = listWeight M := by
  have hsum : (∑ j : Fin M.reverse.length, ((M.reverse).get (Fin.rev j)).1)
      = (∑ j : Fin M.reverse.length, ((M.reverse).get j).1) := by
    refine Finset.sum_equiv (Fin.revPerm : Equiv.Perm (Fin M.reverse.length))
      (f := fun j => ((M.reverse).get (Fin.rev j)).1)
      (g := fun j => ((M.reverse).get j).1) ?_ ?_
    · intro i
      simp
    · intro i _
      simp only [Fin.revPerm_apply]
  rw [hsum, ← List.sum_ofFn]
  change (List.ofFn (Prod.fst ∘ (M.reverse).get)).sum = listWeight M
  rw [← List.map_ofFn, List.ofFn_get]
  simp only [listWeight, List.map_reverse, List.sum_reverse]

lemma listWeight_tmCoe (L : List (ℕ × Polynomial (Ambient F))) :
    listWeight (tmCoe (K := Ambient F) L) = tmWeight L := by
  simp only [listWeight, tmCoe, tmWeight, List.map_map]
  rfl

/-- **The exponent sum of the suffix is the weight of the dropped tail.** -/
lemma suffixList_weight (L : List (ℕ × Polynomial (Ambient F))) :
    (∑ j : Fin (suffixList F L).length, ((suffixList F L).get (Fin.rev j)).1)
      = tmWeight L := by
  have h := listWeight_rev_get (M := tmCoe (K := Ambient F) L)
  rwa [listWeight_tmCoe F] at h

/-- The suffix has weight `w - tmWeight (s.take k)`. -/
lemma T0S_drop_exp_weight {w : ℕ} {hw : 1 ≤ w}
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    {s : List (ℕ × Polynomial (Ambient F))} (hs : s ∈ T0S F w hw) (k : ℕ) :
    (∑ j : Fin (suffixList F (s.drop k)).length,
        ((suffixList F (s.drop k)).get (Fin.rev j)).1) + tmWeight (s.take k) = w := by
  rw [suffixList_weight F, T0S_drop_weight F hs]

/-! ## §6. Step 3, third part: the divisibility `(q-1) ∣ w - w(𝔱)` -/

/-- A polynomial whose coefficients lie in `F_q[θ]` takes a value in `K = F_q(θ)`. -/
lemma eval_mem_ambK (p : Polynomial (Ambient F)) (hp : ∀ j, p.coeff j ∈ ambA F 0) :
    p.eval (ambTheta F) ∈ ambK F := by
  rw [Polynomial.eval_eq_sum_range]
  refine Subfield.sum_mem (ambK F) (fun j _ => ?_)
  exact Subfield.mul_mem (ambK F) (ambA_zero_subset_ambK F (hp j))
    (Subfield.pow_mem (ambK F) (ambTheta_mem_ambK F) j)

/-- ★★★ **Step 3's divisibility** (`(q-1) ∣ w - w(𝔱)` in the exponent-sum form), obtained from
`step3_II_T0` by `Step3Val.dvd_pred_of_v_eq_exp_mul`. -/
theorem dvd_pred_step3_II_T0 (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hk : ((T0S F w hw).filter (fun s => s ≠ tupleListP F (T0exp F w hw v))).sup
      (fun s => ((s.zip (tupleListP F (T0exp F w hw v))).takeWhile
        (fun p => p.1 = p.2)).length) < k)
    (hkl : k < (tupleListP F (T0exp F w hw v)).length)
    (hbmem : ∀ j, (b v).coeff j ∈ ambA F 0)
    (hb0 : (b v).eval (ambTheta F) ≠ 0)
    (hζ : ζ_A F (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
      (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k)) ≠ 0)
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ≠ 0) :
    (Nat.card F - 1) ∣ (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
          (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k) j : ℕ)) := by
  refine dvd_pred_of_v_eq_exp_mul
    (m := ∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
          (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k) j : ℕ))
    (y := (ambPiTilde F) ^ (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
        (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
          (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k) j : ℕ)))
    (u := (b v).eval (ambTheta F) * ambInfHom F (ζ_A F
      (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
        (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k))))
    (v := evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F))
    (hy := ?_) (hu := ?_) (hv := ?_) (hv0 := hf0) (h := step3_II_T0 F w hw b v hk hkl)
  · exact v_ambPiTilde_pow F _
  · obtain ⟨k₁, hk₁⟩ := v_mem_ambK F (eval_mem_ambK F (b v) hbmem) hb0
    obtain ⟨k₂, hk₂⟩ := v_ambInfHom_mem_pred F _ hζ
    refine ⟨k₁ + k₂, ?_⟩
    rw [map_mul, hk₁, hk₂, ← WithZero.exp_add]
    congr 1
    push_cast
    ring
  · exact v_mem_ambK F hfK hf0

/-- ★★★ **Step 3's divisibility, in WEIGHT form**: `(q-1) ∣ w - tmWeight (s₀.take k)`, i.e.
`(q-1)` divides the weight of the part of `𝔰_v` strictly after the prefix `s₀.take k`. -/
theorem dvd_pred_weight_T0 (w : ℕ) (hw : 1 ≤ w)
    [Fintype {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}]
    (b : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} → Polynomial (Ambient F))
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) {k : ℕ}
    (hk : ((T0S F w hw).filter (fun s => s ≠ tupleListP F (T0exp F w hw v))).sup
      (fun s => ((s.zip (tupleListP F (T0exp F w hw v))).takeWhile
        (fun p => p.1 = p.2)).length) < k)
    (hkl : k < (tupleListP F (T0exp F w hw v)).length)
    (hbmem : ∀ j, (b v).coeff j ∈ ambA F 0)
    (hb0 : (b v).eval (ambTheta F) ≠ 0)
    (hζ : ζ_A F (suffixExp F ((tupleListP F (T0exp F w hw v)).drop k)
      (T0S_drop_mem_pos F (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k)) ≠ 0)
    (hfK : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ∈ ambK F)
    (hf0 : evalSeriesGen (tmF (Nat.card F) (ambOmega F) w (T0S F w hw) (T0cf F w hw b)
      ((tupleListP F (T0exp F w hw v)).take k)) (ambTheta F) ≠ 0) :
    (Nat.card F - 1) ∣ (w - tmWeight ((tupleListP F (T0exp F w hw v)).take k)) := by
  have h1 := dvd_pred_step3_II_T0 F w hw b v hk hkl hbmem hb0 hζ hfK hf0
  have h2 := T0S_drop_exp_weight F (s := tupleListP F (T0exp F w hw v))
    (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩) k
  have hS : (∑ j : Fin (suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).length,
      ((suffixList F ((tupleListP F (T0exp F w hw v)).drop k)).get (Fin.rev j)).1)
      = w - tmWeight ((tupleListP F (T0exp F w hw v)).take k) := by
    omega
  rw [← hS]
  exact h1

end ZagierHoffmanPositiveChar







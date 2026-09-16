/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.DegCountAnyF
import Submission.ZagierHoffmanProof.StepL202

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# `F_q`-linear independence of the Hoffman MZVs of a fixed weight

Thakur's conjecture in positive characteristic predicts that the MZVs of a fixed weight are
linearly independent over the base field `F_q`.  The conjecture fails for large weights in
general, but it holds for **all** weights on the Hoffman set `𝒯_w` (entries `≤ q`, last entry
`< q`): distinct Hoffman tuples of the same weight have distinct base-`q` codes, hence distinct
`degExp`, and the standard "distinct valuations" argument (`DegAnyF.zeta_linearIndependent_le_card`)
applies.

The main results here are:
* `degExp_shapeTuple_injective`: the degree exponent is injective on the Hoffman shapes;
* `linearIndependent_shape`: no nontrivial `F_q`-linear relation between the `d(w)` Hoffman MZVs
  of weight `w` (parametrised by their shapes);
* `shapeEquivT`: the canonical bijection between the weight-`w` Hoffman shapes and `𝒯 F w`;
* `linearIndependent_T`: the same independence statement for the set `𝒯 F w` itself;
* `bloExp_eq_degExp` and `zeta_linearIndependent_entriesVal`: the linear-independence criterion
  generalised to `EntriesVal` tuples (entries `q^k·m` with `m ≤ q`), and the corollary
  `zeta_frobenius_orbit_linearIndependent` for the Frobenius orbit `k ↦ ζ_A(q^k·𝔰)`.

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 1. Degree injectivity on Hoffman shapes -/

/-- ★ **Distinct Hoffman shapes of the same weight have distinct degrees `degExp`.** -/
theorem degExp_shapeTuple_injective {w : ℕ} (hw : 1 ≤ w) :
    Function.Injective (fun x : ShapeT F w w => degExp F (shapeTuple F x)) := by
  intro x y hxy
  have hwxy : tupleWeight (shapeTuple F x) = tupleWeight (shapeTuple F y) := by
    rw [tupleWeight, tupleWeight, shapeTuple_weight F x, shapeTuple_weight F y]
  have hcode : tupleCode F (shapeTuple F x) = tupleCode F (shapeTuple F y) := by
    have hxy0 : degExp F (shapeTuple F x) = degExp F (shapeTuple F y) := hxy
    have h3 := degExp_pred_mul_eq_code F (shapeTuple F x)
    have h4 := degExp_pred_mul_eq_code F (shapeTuple F y)
    rw [hxy0] at h3
    have hwx' : ((tupleWeight (shapeTuple F x) : ℕ) : ℤ)
        = ((tupleWeight (shapeTuple F y) : ℕ) : ℤ) := by rw [hwxy]
    have hqne : (Nat.card F : ℤ) ≠ 0 := by have := card_ge_two F; omega
    have h5 : (Nat.card F : ℤ)
        * (((tupleCode F (shapeTuple F x) : ℕ) : ℤ) - ((tupleWeight (shapeTuple F x) : ℕ) : ℤ))
        = (Nat.card F : ℤ)
        * (((tupleCode F (shapeTuple F y) : ℕ) : ℤ) - ((tupleWeight (shapeTuple F y) : ℕ) : ℤ)) := by
      rw [← h3, ← h4]
    have h6 := mul_left_cancel₀ hqne h5
    have h7 : ((tupleCode F (shapeTuple F x) : ℕ) : ℤ) = ((tupleCode F (shapeTuple F y) : ℕ) : ℤ) := by
      linarith
    exact_mod_cast h7
  obtain ⟨h, htuples⟩ := tupleCode_injective F (shapeTuple F x) (shapeTuple F y)
    (fun i => shapeTuple_le F x i) (fun i => shapeTuple_le F y i) hcode
  have hmark : (x.1.1 : ℕ) = (y.1.1 : ℕ) := by omega
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hmark
  · funext i
    by_cases hi : (i : ℕ) ≤ (x.1.1 : ℕ)
    · have hxi : (i : ℕ) < (x.1.1 : ℕ) + 1 := by omega
      have hyi : (i : ℕ) ≤ (y.1.1 : ℕ) := by omega
      apply Fin.ext
      have key := htuples ⟨(i : ℕ), hxi⟩
      have hidx : (h ▸ ⟨(i : ℕ), hxi⟩ : Fin ((y.1.1 : ℕ) + 1)) = ⟨(i : ℕ), by omega⟩ := by
        apply Fin.ext
        rw [fin_cast_val h ⟨(i : ℕ), hxi⟩]
      have e2 : (shapeTuple F y (h ▸ ⟨(i : ℕ), hxi⟩) : ℕ)
          = (shapeTuple F y ⟨(i : ℕ), by omega⟩ : ℕ) := by
        rw [hidx]
      rw [← shapeTuple_val_apply F x hi, ← shapeTuple_val_apply F y hyi, ← e2]
      exact congrArg (fun t : ℕ+ => (t : ℕ)) key
    · have hxi : (x.1.1 : ℕ) < (i : ℕ) := by omega
      have hyi : (y.1.1 : ℕ) < (i : ℕ) := by omega
      apply Fin.ext
      rw [x.2.2.2.1 i hxi, y.2.2.2.1 i hyi]

/-! ## 2. `F_q`-linear independence of the Hoffman MZVs -/

/-- ★★ **No nontrivial `F_q`-linear relation between the Hoffman MZVs of weight `w`**
(the shape-parametrised form).  This is Thakur's conjecture for the Hoffman set, in every weight
and over every finite field. -/
theorem linearIndependent_shape {w : ℕ} (hw : 1 ≤ w) (c : ShapeT F w w → F)
    (h : (∑ x : ShapeT F w w, cst F (c x) * ζ_A F (shapeTuple F x)) = 0) :
    ∀ x, c x = 0 := by
  classical
  exact zeta_linearIndependent_le_card F
    (fun x : ShapeT F w w => (⟨(x.1.1 : ℕ) + 1, shapeTuple F x⟩ : Σ r : ℕ, Fin r → ℕ+))
    (fun x => Nat.succ_le_succ (Nat.zero_le _))
    (fun x j => shapeTuple_le F x j)
    (fun x y hxy => degExp_shapeTuple_injective F hw hxy)
    c h

/-! ## 3. The `EntriesVal` generalisation (entries `q^k·m`, `m ≤ q`) -/

/-- ★ `bloExp r 𝔰 (r-1)` is the linear degree exponent `degExp 𝔰`. -/
theorem bloExp_eq_degExp : ∀ (r : ℕ) (𝔰 : Fin r → ℕ+),
    bloExp F r 𝔰 (r - 1) = degExp F 𝔰 := by
  intro r
  induction r with
  | zero => intro 𝔰; rw [bloExp, degExp]; simp
  | succ r ih =>
      intro 𝔰
      cases r with
      | zero =>
          rw [bloExp_one, degExp_fin_one]
          simp [Se, Sexp]
      | succ k =>
          have ihk : bloExp F (k + 1) (expTail 𝔰) k = degExp F (expTail 𝔰) := ih (expTail 𝔰)
          rw [show (k + 1 + 1 - 1 : ℕ) = k + 1 from rfl, bloExp_succ F k 𝔰 (k + 1), ihk,
            degExp_cons F (r := k + 1) 𝔰]
          rfl

/-- ★★★ **The exact degree for `EntriesVal` tuples**: this generalises `DegAnyF.val_zeta_le_card`
(entries `≤ q`) to all tuples whose entries are `q^k·m` with `m ≤ q`. -/
theorem val_zeta_entriesVal {r : ℕ} (hr : 1 ≤ r) (𝔰 : Fin r → ℕ+) (h𝔰 : EntriesVal F 𝔰) :
    Valued.v (ζ_A F 𝔰) = WithZero.exp (-(degExp F 𝔰)) := by
  rw [val_zeta_val F (by omega) 𝔰 h𝔰, bloExp_eq_degExp F r 𝔰]

/-- ★★ **Linear independence over the prime field** of MZVs whose entries are valuation-good
(`q^k·m` with `m ≤ q`) and whose degrees are pairwise distinct.  Same argument as
`DegAnyF.zeta_linearIndependent_le_card`, with the exact-degree input `val_zeta_entriesVal`. -/
theorem zeta_linearIndependent_entriesVal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝔰 : ι → Σ r : ℕ, Fin r → ℕ+)
    (hr : ∀ i, 1 ≤ (𝔰 i).1) (hval : ∀ i, EntriesVal F (𝔰 i).2)
    (hdeg : Function.Injective (fun i => degExp F (𝔰 i).2))
    (c : ι → F) (h : (∑ i, cst F (c i) * ζ_A F (𝔰 i).2) = 0) :
    ∀ i, c i = 0 := by
  classical
  set I : Finset ι := Finset.univ.filter (fun i => c i ≠ 0) with hI
  by_contra hcon
  simp only [not_forall] at hcon
  obtain ⟨i0, hi0⟩ := hcon
  have hInon : I.Nonempty := ⟨i0, by simp [hI, hi0]⟩
  obtain ⟨j0, hj0I, hj0min⟩ := Finset.exists_min_image I (fun i => degExp F (𝔰 i).2) hInon
  have hcj0 : c j0 ≠ 0 := by
    have h' := hj0I
    rw [hI] at h'
    simpa using h'
  have hsub : (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2)
      = ∑ i, cst F (c i) * ζ_A F (𝔰 i).2 := by
    rw [hI]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro i _ hi
    have hci : c i = 0 := by
      by_contra hc
      exact hi (by simp [hc])
    have hz : cst F (0 : F) = 0 := map_zero (cstHom F)
    rw [hci, hz, zero_mul]
  have hv : ∀ i ∈ I \ {j0},
      Valued.v (cst F (c i) * ζ_A F (𝔰 i).2) < Valued.v (cst F (c j0) * ζ_A F (𝔰 j0).2) := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hi
    obtain ⟨hiI, hij⟩ := hi
    have hci : c i ≠ 0 := by
      have h' := hiI
      rw [hI] at h'
      simpa using h'
    rw [map_mul, map_mul, v_cst_of_ne_zero F hci, v_cst_of_ne_zero F hcj0, one_mul, one_mul,
      val_zeta_entriesVal F (hr i) (𝔰 i).2 (hval i),
      val_zeta_entriesVal F (hr j0) (𝔰 j0).2 (hval j0), WithZero.exp_lt_exp]
    have h2 := hj0min i hiI
    have h3 : degExp F (𝔰 i).2 ≠ degExp F (𝔰 j0).2 := fun hh => hij (hdeg hh)
    omega
  have hval' := Valuation.map_sum_eq_of_lt (v := Valued.v) hj0I hv
  have hzero : Valued.v (∑ i ∈ I, cst F (c i) * ζ_A F (𝔰 i).2) = 0 := by
    rw [hsub, h, map_zero]
  rw [hval', map_mul, v_cst_of_ne_zero F hcj0, one_mul,
    val_zeta_entriesVal F (hr j0) (𝔰 j0).2 (hval j0)] at hzero
  exact WithZero.exp_ne_zero hzero

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 4. The shape ↔ `𝒯_w` bijection and the `𝒯_w`-form of linear independence -/

/-- **The tuple of the shape of a Hoffman tuple is the tuple** (the reverse round trip): the
entries of `shapeTuple (tupleShape s)` are the entries of `s`. -/
lemma shapeTuple_tupleShape {w : ℕ} (hw : 1 ≤ w) {r : ℕ} (hr1 : 1 ≤ r) (hrw : r ≤ w)
    (s : Fin r → ℕ+) (hsum : (∑ i : Fin r, ((s i : ℕ+)) : ℕ) = w)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F)
    (i : Fin ((tupleShape F w hw r hr1 hrw s hsum hfirst hlast).1.1 + 1)) :
    (shapeTuple F (tupleShape F w hw r hr1 hrw s hsum hfirst hlast) i : ℕ)
      = (s ⟨(i : ℕ), by
            have h := tupleShape_depth F hw hr1 hrw s hsum hfirst hlast
            have hi := i.isLt
            omega⟩ : ℕ) := by
  have hw' : (i : ℕ) < w := by
    have h := ShapeT_depth_le F (tupleShape F w hw r hr1 hrw s hsum hfirst hlast)
    have hi := i.isLt
    omega
  have hle : (i : ℕ)
      ≤ ((tupleShape F w hw r hr1 hrw s hsum hfirst hlast).1.1 : ℕ) := by
    have h := tupleShape_depth F hw hr1 hrw s hsum hfirst hlast
    have hi := i.isLt
    omega
  refine (shapeTuple_val_apply F (tupleShape F w hw r hr1 hrw s hsum hfirst hlast)
    (i := ⟨(i : ℕ), hw'⟩) hle).trans ?_
  have hir : (i : ℕ) < r := by
    have h := tupleShape_depth F hw hr1 hrw s hsum hfirst hlast
    have hi := i.isLt
    omega
  exact tupleShape_entry F hw hr1 hrw s hsum hfirst hlast (i := ⟨(i : ℕ), hw'⟩) hir

/-- The shape-to-MZV map of a weight-`w` Hoffman tuple. -/
noncomputable def shapeVal {w : ℕ} (hw : 1 ≤ w) (x : ShapeT F w w) :
    {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯 F w} :=
  ⟨ζ_A F (shapeTuple F x), shapeTuple_mem_T F (Nat.one_le_iff_ne_zero.mp hw) x⟩

/-- The shape-to-MZV map is injective. -/
lemma shapeVal_injective {w : ℕ} (hw : 1 ≤ w) : Function.Injective (shapeVal F hw) := by
  intro x y hxy
  exact shapeTuple_zeta_injective F hw (congrArg Subtype.val hxy)

/-- The shape-to-MZV map is surjective. -/
lemma shapeVal_surjective {w : ℕ} (hw : 1 ≤ w) : Function.Surjective (shapeVal F hw) := by
  classical
  intro v
  obtain ⟨r, hr⟩ := (mem_T F w v.val).mp v.2
  obtain ⟨s, hsum, hfirst, hlast, hζ⟩ := (mem_Taux F w r v.val).mp hr
  have hr1 : 1 ≤ (r : ℕ) := Nat.succ_le_of_lt r.pos
  have hrw : (r : ℕ) ≤ w := by
    have hc := card_le_sum_pnat (r : ℕ) s
    rw [hsum] at hc
    exact hc
  refine ⟨tupleShape F w hw (r : ℕ) hr1 hrw s hsum hfirst hlast, ?_⟩
  apply Subtype.ext
  have hmark : ((tupleShape F w hw (r : ℕ) hr1 hrw s hsum hfirst hlast).1.1 : ℕ) + 1
      = (r : ℕ) := tupleShape_depth F hw hr1 hrw s hsum hfirst hlast
  rw [shapeVal, ← hζ]
  refine ζ_A_eq_of_reindex F hmark _ _ ?_
  intro i
  exact Subtype.ext (shapeTuple_tupleShape F hw hr1 hrw s hsum hfirst hlast i)

/-- ★★ **The canonical bijection between the weight-`w` Hoffman shapes and the set `𝒯 F w`.**
(As a byproduct, `ncard (𝒯 F w) = hoffCount F w = d F w`.) -/
noncomputable def shapeEquivT {w : ℕ} (hw : 1 ≤ w) :
    ShapeT F w w ≃ {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯 F w} :=
  Equiv.ofBijective (shapeVal F hw) ⟨shapeVal_injective F hw, shapeVal_surjective F hw⟩

/-- ★★ **No nontrivial `F_q`-linear relation between the elements of `𝒯 F w`** (the
`𝒯_w`-form, transported along the shape bijection `shapeEquivT`). -/
theorem linearIndependent_T {w : ℕ} (hw : 1 ≤ w)
    (c : {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯 F w} → F)
    (h : (∑ x : ShapeT F w w, cst F (c (shapeEquivT F hw x)) * ζ_A F (shapeTuple F x)) = 0) :
    ∀ v, c v = 0 := by
  classical
  have hc := linearIndependent_shape F hw (fun x => c (shapeEquivT F hw x)) h
  intro v
  obtain ⟨x, rfl⟩ := (shapeEquivT F hw).surjective v
  exact hc x

/-! ## 5. The Frobenius orbit -/

/-- The `k`-th Frobenius iterate of a tuple, entrywise. -/
lemma scaleTuple_iter_eq (k : ℕ) {r : ℕ} (𝔰 : Fin r → ℕ+) :
    (scaleTuple F)^[k] 𝔰 = fun i => (qExp F) ^ k * 𝔰 i := by
  induction k with
  | zero => funext i; simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      funext i
      simp [scaleTuple, pow_succ', mul_assoc]

/-- The entries of the `k`-th Frobenius iterate. -/
lemma scaleTuple_iter_apply (k : ℕ) {r : ℕ} (𝔰 : Fin r → ℕ+) (i : Fin r) :
    (((scaleTuple F)^[k] 𝔰) i : ℕ) = (Nat.card F) ^ k * (𝔰 i : ℕ) := by
  rw [scaleTuple_iter_eq F k 𝔰, PNat.mul_coe, PNat.pow_coe]
  rfl

/-- The degree exponent of a Frobenius iterate is scaled by `q^k`. -/
lemma degExp_scaleTuple_iter (k : ℕ) {r : ℕ} (𝔰 : Fin r → ℕ+) :
    degExp F ((scaleTuple F)^[k] 𝔰) = ((Nat.card F) ^ k : ℤ) * degExp F 𝔰 := by
  rw [degExp, degExp, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [scaleTuple_iter_apply F k 𝔰 i]
  push_cast
  ring

/-- Frobenius iterates of valuation-good tuples are valuation-good. -/
lemma entriesVal_scaleTuple_iter (k : ℕ) {r : ℕ} {𝔰 : Fin r → ℕ+}
    (h𝔰 : EntriesVal F 𝔰) : EntriesVal F ((scaleTuple F)^[k] 𝔰) := by
  intro i
  rw [scaleTuple_iter_eq F k 𝔰]
  exact entryVal_pow F k (𝔰 i) (h𝔰 i)

/-- ★★ **The Frobenius orbit `k ↦ ζ_A(q^k·𝔰)` is `F_q`-linearly independent** (for a
valuation-good tuple `𝔰` with nonzero degree). -/
theorem zeta_frobenius_orbit_linearIndependent {r : ℕ} (hr : 1 ≤ r) {𝔰 : Fin r → ℕ+}
    (h𝔰 : EntriesVal F 𝔰) (hD : degExp F 𝔰 ≠ 0) (n : ℕ) (c : Fin (n + 1) → F)
    (h : (∑ k : Fin (n + 1), cst F (c k) * ζ_A F ((scaleTuple F)^[(k : ℕ)] 𝔰)) = 0) :
    ∀ k, c k = 0 := by
  classical
  refine zeta_linearIndependent_entriesVal F
    (fun k : Fin (n + 1) => (⟨r, (scaleTuple F)^[(k : ℕ)] 𝔰⟩ : Σ r : ℕ, Fin r → ℕ+))
    (fun k => hr) (fun k => entriesVal_scaleTuple_iter F (k : ℕ) h𝔰) ?_ c h
  intro k₁ k₂ hk
  have hq : 2 ≤ Nat.card F := two_le_card F
  have h1 : ((Nat.card F) ^ (k₁ : ℕ) : ℤ) = ((Nat.card F) ^ (k₂ : ℕ) : ℤ) := by
    have h2 : ((Nat.card F) ^ (k₁ : ℕ) : ℤ) * degExp F 𝔰
        = ((Nat.card F) ^ (k₂ : ℕ) : ℤ) * degExp F 𝔰 := by
      rw [← degExp_scaleTuple_iter F (k₁ : ℕ) 𝔰, ← degExp_scaleTuple_iter F (k₂ : ℕ) 𝔰]
      exact hk
    exact mul_right_cancel₀ hD h2
  exact Fin.ext (Nat.pow_right_injective hq (Nat.cast_inj.mp h1))

end ZagierHoffmanPositiveChar

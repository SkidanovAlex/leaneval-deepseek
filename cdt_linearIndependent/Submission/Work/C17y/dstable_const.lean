import Mathlib
import Submission.CDT.RatFuncConstants
import Submission.Work.GenShared.periods_defs

/-!
# `dRat`-stable subspaces of `K^m` contain nonzero constant vectors

For `K = ℂ(x)` and a `K`-subspace `V ≤ K^m` stable under the componentwise formal derivative
`dRat`, nonvanishing of `V` forces `V ∩ ℂ^m ≠ 0` (`Work.C17y.dstable_const`).

The proof is an induction on the number `m` of coordinates ("drop the last coordinate"):

* if all nonzero elements of `V` have a *nonzero* last coordinate, the last coordinate functional
  is injective on `V` (so `dim_K V = 1`): scaling a nonzero `v ∈ V` to make its last coordinate
  equal to `1`, the vector `w = (v_last)⁻¹ • v ∈ V` has last coordinate `1`, whence
  `(Dw)_last = dRat 1 = 0` and injectivity gives `Dw = 0`; every coordinate of `w` is then a
  constant (`Submission.CDT.exists_const_of_dRat_eq_zero`) and `w` is a nonzero constant vector.
  This argument only needs *some* coordinate functional injective on `V`, see
  `Work.C17y.dstable_const_of_coord_injective`;
* otherwise the submodule `W ≤ V` of vectors with vanishing last coordinate is nonzero; it is
  again `dRat`-stable and (as all its elements vanish in the last coordinate) it is recovered from
  its `Fin.init`-image, to which the induction hypothesis applies
  (`Work.C17y.init_map_plumbing`).
-/

namespace Work.C17y

open Submission.CDT

noncomputable section

/-! ## Auxiliary linear maps -/

/-- Projection onto the last coordinate. -/
def lastProj (m : ℕ) : (Fin (m + 1) → RatFunc ℂ) →ₗ[RatFunc ℂ] RatFunc ℂ where
  toFun v := v (Fin.last m)
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

lemma lastProj_apply (m : ℕ) (v : Fin (m + 1) → RatFunc ℂ) :
    lastProj m v = v (Fin.last m) := rfl

lemma mem_lastKer (m : ℕ) (v : Fin (m + 1) → RatFunc ℂ) :
    v ∈ LinearMap.ker (lastProj m) ↔ v (Fin.last m) = 0 := by
  rw [LinearMap.mem_ker, lastProj_apply]

/-- The linear map `x ↦ Fin.snoc x 0`, i.e. "append a zero in the last coordinate". -/
def snocLM (m : ℕ) : (Fin m → RatFunc ℂ) →ₗ[RatFunc ℂ] (Fin (m + 1) → RatFunc ℂ) where
  toFun x := Fin.snoc x 0
  map_add' := by
    intro x y; funext j
    refine Fin.lastCases ?_ ?_ j <;> simp [Fin.snoc_castSucc, Fin.snoc_last]
  map_smul' := by
    intro a x; funext j
    refine Fin.lastCases ?_ ?_ j <;> simp [Fin.snoc_castSucc, Fin.snoc_last]

lemma snocLM_apply (m : ℕ) (x : Fin m → RatFunc ℂ) :
    snocLM m x = Fin.snoc x (0 : RatFunc ℂ) := rfl

/-- `Fin.snoc` commutes with the scalar embedding `ℂ → ℂ(x)`. -/
lemma snoc_algebraMap (m : ℕ) (c : Fin m → ℂ) :
    Fin.snoc (fun i => algebraMap ℂ (RatFunc ℂ) (c i)) (0 : RatFunc ℂ)
      = fun j => algebraMap ℂ (RatFunc ℂ) ((Fin.snoc c (0 : ℂ) : Fin (m + 1) → ℂ) j) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [Fin.snoc_last]
  · intro i; simp [Fin.snoc_castSucc]

/-- `Fin.snoc` commutes with the componentwise derivation `dRat`. -/
lemma snoc_dRat (m : ℕ) (x : Fin m → RatFunc ℂ) :
    Fin.snoc (fun i => dRat (x i)) (0 : RatFunc ℂ)
      = fun j => dRat ((Fin.snoc x (0 : RatFunc ℂ) : Fin (m + 1) → RatFunc ℂ) j) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp [Fin.snoc_last]
  · intro i; simp [Fin.snoc_castSucc]

/-! ## The two halves of the induction step -/

/-- **One-dimensional case.**  If `V ≤ K^m` is `dRat`-stable, nonzero, and the `i`-th coordinate
functional is injective on `V`, then `V` contains a nonzero constant vector: scaling a nonzero
`v ∈ V` so that its `i`-th coordinate is `1`, its derivative lies in `V` and vanishes at `i`,
hence is `0` by injectivity, so every coordinate of the scaled vector is constant. -/
theorem dstable_const_of_coord_injective {m : ℕ} (i : Fin m)
    (V : Submodule (RatFunc ℂ) (Fin m → RatFunc ℂ))
    (hV : ∀ v ∈ V, (fun j => dRat (v j)) ∈ V) (hne : V ≠ ⊥)
    (hpiv : ∀ v ∈ V, v i = 0 → v = 0) :
    ∃ c : Fin m → ℂ, c ≠ 0 ∧ (fun j => algebraMap ℂ (RatFunc ℂ) (c j)) ∈ V := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvi : v i ≠ 0 := fun h => hv0 (hpiv v hv h)
  set w : Fin m → RatFunc ℂ := (v i)⁻¹ • v with hwdef
  have hw : w ∈ V := V.smul_mem _ hv
  have hwi : w i = 1 := by
    rw [hwdef, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hvi]
  have hDw : (fun j => dRat (w j)) ∈ V := hV w hw
  have hDwi : (fun j => dRat (w j)) i = 0 := by
    show dRat (w i) = 0
    rw [hwi, dRat_one]
  have hzero : (fun j => dRat (w j)) = 0 := hpiv _ hDw hDwi
  have hconst : ∀ j, ∃ c : ℂ, w j = algebraMap ℂ (RatFunc ℂ) c := fun j =>
    exists_const_of_dRat_eq_zero (by have h := congrFun hzero j; simpa using h)
  choose c hc using hconst
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    have h1 : algebraMap ℂ (RatFunc ℂ) (c i) = 1 := by rw [← hc i, hwi]
    have h2 : algebraMap ℂ (RatFunc ℂ) (c i) = 0 := by rw [hc0]; simp
    rw [h2] at h1
    exact zero_ne_one h1
  · have hw_eq : (fun j => algebraMap ℂ (RatFunc ℂ) (c j)) = w := by
      funext j; exact (hc j).symm
    rw [hw_eq]; exact hw

/-- **Induction step, plumbing.**  A `dRat`-stable submodule `W ≤ K^{m+1}` all of whose elements
vanish in the last coordinate has an `init`-image `W' ≤ K^m` (namely the preimage of `W` under
`x ↦ Fin.snoc x 0`) which is again `dRat`-stable and nonzero, and every nonzero constant vector of
`W'` lifts to a constant vector of `W` (append `0` in the last coordinate). -/
theorem init_map_plumbing {m : ℕ} (W : Submodule (RatFunc ℂ) (Fin (m + 1) → RatFunc ℂ))
    (hker : ∀ v ∈ W, v (Fin.last m) = 0)
    (hW : ∀ v ∈ W, (fun j => dRat (v j)) ∈ W) (hne : W ≠ ⊥) :
    ∃ W' : Submodule (RatFunc ℂ) (Fin m → RatFunc ℂ),
      (∀ v ∈ W', (fun j => dRat (v j)) ∈ W') ∧ W' ≠ ⊥ ∧
        ∀ c : Fin m → ℂ, (fun i => algebraMap ℂ (RatFunc ℂ) (c i)) ∈ W' →
          (fun j => algebraMap ℂ (RatFunc ℂ) ((Fin.snoc c (0 : ℂ) : Fin (m + 1) → ℂ) j)) ∈ W := by
  refine ⟨W.comap (snocLM m), ?_, ?_, ?_⟩
  · -- `W'` is `dRat`-stable
    intro x hx
    have hxW : Fin.snoc x (0 : RatFunc ℂ) ∈ W := by
      have h := Submodule.mem_comap.mp hx
      rwa [snocLM_apply] at h
    have h1 : Fin.snoc (fun i => dRat (x i)) (0 : RatFunc ℂ) ∈ W := by
      have h2 := hW _ hxW
      rwa [← snoc_dRat] at h2
    rw [Submodule.mem_comap, snocLM_apply]
    exact h1
  · -- `W' ≠ ⊥`
    intro hbot
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hmem : Fin.init v ∈ W.comap (snocLM m) := by
      rw [Submodule.mem_comap, snocLM_apply,
        show Fin.snoc (Fin.init v) (0 : RatFunc ℂ) = v from by
          rw [← hker v hv]; exact Fin.snoc_init_self v]
      exact hv
    rw [hbot] at hmem
    have hinit0 : Fin.init v = 0 := by simpa using hmem
    have : v = 0 := by
      rw [← Fin.snoc_init_self v, hinit0, hker v hv]
      funext j
      refine Fin.lastCases ?_ ?_ j <;> simp [Fin.snoc_castSucc, Fin.snoc_last]
    exact hv0 this
  · -- constant vectors lift
    intro c hc
    have hcW : Fin.snoc (fun i => algebraMap ℂ (RatFunc ℂ) (c i)) (0 : RatFunc ℂ) ∈ W := by
      have h := Submodule.mem_comap.mp hc
      rwa [snocLM_apply] at h
    rwa [← snoc_algebraMap m c]

/-- Induction statement: `dRat`-stable nonzero subspaces of `K^m` contain a nonzero constant
vector, for every number `m` of coordinates. -/
theorem dstable_const_aux : ∀ m : ℕ, ∀ V : Submodule (RatFunc ℂ) (Fin m → RatFunc ℂ),
    (∀ v ∈ V, (fun j => dRat (v j)) ∈ V) → V ≠ ⊥ →
    ∃ c : Fin m → ℂ, c ≠ 0 ∧ (fun j => algebraMap ℂ (RatFunc ℂ) (c j)) ∈ V := by
  intro m
  induction m with
  | zero =>
      -- `Fin 0 → ℂ(x)` is a subsingleton, so the only submodule is `⊥`
      intro V _ hne
      exact absurd (le_bot_iff.mp (fun v _ => Subsingleton.elim v 0)) hne
  | succ m ih =>
      intro V hV hne
      by_cases hW : (V ⊓ LinearMap.ker (lastProj m)) = ⊥
      · -- the last coordinate functional is injective on `V`
        refine dstable_const_of_coord_injective (Fin.last m) V hV hne ?_
        intro v hv hvi
        have hmem : v ∈ V ⊓ LinearMap.ker (lastProj m) :=
          Submodule.mem_inf.mpr ⟨hv, (mem_lastKer m v).mpr hvi⟩
        rw [hW] at hmem
        simpa using hmem
      · -- drop the last coordinate
        have hker : ∀ v ∈ V ⊓ LinearMap.ker (lastProj m), v (Fin.last m) = 0 := by
          intro v hv
          exact (mem_lastKer m v).mp (Submodule.mem_inf.mp hv).2
        have hds : ∀ v ∈ V ⊓ LinearMap.ker (lastProj m),
            (fun j => dRat (v j)) ∈ V ⊓ LinearMap.ker (lastProj m) := by
          intro v hv
          obtain ⟨hvV, hvK⟩ := Submodule.mem_inf.mp hv
          refine Submodule.mem_inf.mpr ⟨hV v hvV, ?_⟩
          rw [mem_lastKer]
          show dRat (v (Fin.last m)) = 0
          rw [(mem_lastKer m v).mp hvK, dRat_zero]
        obtain ⟨W', hW'ds, hW'ne, hlift⟩ :=
          init_map_plumbing (V ⊓ LinearMap.ker (lastProj m)) hker hds hW
        obtain ⟨c, hc0, hcmem⟩ := ih W' hW'ds hW'ne
        refine ⟨(Fin.snoc c (0 : ℂ) : Fin (m + 1) → ℂ), ?_, ?_⟩
        · -- the appended zero keeps the constant vector nonzero
          intro h0
          have : c = 0 := by
            funext i
            have h := congrFun h0 i.castSucc
            rw [Fin.snoc_castSucc] at h
            simpa using h
          exact hc0 this
        · exact (Submodule.mem_inf.mp (hlift c hcmem)).1

/-- **A `dRat`-stable `K`-subspace of `K^m` contains a nonzero constant vector** (`K = ℂ(x)`).

Let `V ⊆ K^m` be a `K`-subspace stable under the derivation `dRat` (the formal derivative of a
rational function, `Submission.CDT.dRat`), componentwise, i.e. `v ∈ V → (fun j => dRat (v j)) ∈ V`.
If `V ≠ 0` then `V` contains a nonzero vector all of whose coordinates are constants
`algebraMap ℂ K c` (so `V ∩ (ℂ^m) ≠ 0`).

Proof sketch (the "constant echelon"): take a `K`-basis `v_1,…,v_d` of `V` with `d = finrank K V`,
let `Ψ` be the `d × m` matrix with rows `v_i`, choose `d` columns `J` with
`det (Ψ.submatrix id J) ≠ 0` (e.g. via `Work.ZeroEst.exists_det_submatrix_ne_zero`, which works over
any field), and set `E := (Ψ.submatrix id J)⁻¹ * Ψ`.  Writing `dRat (v i) = Σ_j M i j • v j`, one has
`Ψ' = M * Ψ` (entrywise `dRat`, `M` arbitrary) and hence `Ψ_J' = M * Ψ_J`, so
`Ψ_J * E' = 0`; cancelling the invertible factor `Ψ_J` gives `E' = 0`: every entry of `E` is a
constant (use `Submission.CDT.exists_const_of_dRat_eq_zero`).  Finally `Ψ = Ψ_J * E` shows that every
row of `E` is a `K`-linear combination of the rows of `Ψ`, hence lies in `V`; and `E ≠ 0` since
`Ψ = Ψ_J E ≠ 0`, so some row of `E` is a nonzero constant vector in `V`.

(Implementation: an induction on `m` that drops the last coordinate; see
`Work.C17y.dstable_const_of_coord_injective` and `Work.C17y.init_map_plumbing`.) -/
theorem dstable_const {m : ℕ} (V : Submodule (RatFunc ℂ) (Fin m → RatFunc ℂ))
    (hV : ∀ v ∈ V, (fun j => Submission.CDT.dRat (v j)) ∈ V) (hne : V ≠ ⊥) :
    ∃ c : Fin m → ℂ, c ≠ 0 ∧ (fun j => algebraMap ℂ (RatFunc ℂ) (c j)) ∈ V :=
  dstable_const_aux m V hV hne

end

end Work.C17y

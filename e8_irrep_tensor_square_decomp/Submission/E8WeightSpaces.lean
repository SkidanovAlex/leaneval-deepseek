import Submission.E8LocallyNilpotent
import Submission.Commons.Data.List.finite_setOf_count_eq

/-!
# The weight-space decomposition of the irreducible quotient `L(ω₁+ω₈) = V ⧸ N`

This file builds the weight-space structure of the simple quotient `L = V ⧸ N` of the Verma
module `V` by its unique maximal submodule.

* `Wm_finite` : the word space `Wm m` (spanned by the words of letter-multiplicity vector `m`) is
  finite-dimensional -- it is spanned by the finitely many words with content `m`;
* `Lw m := (Wm m).map N.mkQ` : the image of `Wm m` in `L`, finite-dimensional (`Lw_finite`) and
  spanning (`iSup_Lw_eq_top`);
* the action of the `H`-generators on `Lw m` is the scalar `wt m i` (`endU_h_apply_mem_Lw`);
* `endU` : the ℂ-linear endomorphism of `L` attached to `u : U(e₈)`, so that the `E`/`F`-generators
  act between neighbouring weight spaces (`endU_e_apply_mem_Lw`, `endU_f_apply_mem_Lw`);
* the projection onto a single weight space (the "killer" product of `VermaWeight` descended to
  `L`), giving the **uniqueness of the weight decomposition** (`eq_zero_of_sum_eq_zero`).

Everything is indexed by the *multiplicity vector* `m : Fin 8 → ℕ` of a word; the corresponding
weight is `wt m = λ - ∑ mᵢ αᵢ` (with `wt_injective`), and `wtZ m` is its integral form
(`wt_eq_cast`).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section
open scoped BigOperators

namespace Submission.E8WeightSpaces

open Submission.StarModule (wordElt wordElt_nil bas bas_apply Lop Lop_wordElt Eword wrho
  Eop_apply)
open Submission.StarQuotient (Hbar Ebar Lbar J V Hbar_mk Ebar_mk Lbar_mk)
open Submission.VermaWeight
open Submission.E8NullVector (f_smul_eq e_smul_eq h_smul_eq)

abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

/-! ## The integral form of the weight of a multiplicity vector -/

/-- The weight of the word space of multiplicity vector `m`, in integral form:
`wtZ m i = (ω₁+ω₈)ᵢ - ∑ a, m a * A i a`. -/
def wtZ (m : Fin 8 → ℕ) : Fin 8 → ℤ :=
  fun i => (if i = 0 then 1 else 0) + (if i = 7 then 1 else 0) - ∑ a : Fin 8, (m a : ℤ) * E8 i a

lemma wt_eq_cast (m : Fin 8 → ℕ) (i : Fin 8) : wt m i = ((wtZ m i : ℤ) : ℂ) := by
  simp only [wt_def, wtZ, Submission.E8Weights.omegaOnePlusOmegaEight, E8]
  push_cast
  ring

lemma wtZ_injective : Function.Injective wtZ := by
  intro m m' h
  refine wt_injective ?_
  funext i
  rw [wt_eq_cast, wt_eq_cast, h]

/-! ## Finiteness of the word spaces -/

/-- The defining set of `Wm m`: the word vectors of content `m`. -/
def WmSet (m : Fin 8 → ℕ) : Set V :=
  {x : V | ∃ w : List (Fin 8), (∀ i, w.count i = m i) ∧
    x = (Submodule.Quotient.mk (wordElt w) : V)}

lemma Wm_eq_span_WmSet (m : Fin 8 → ℕ) : Wm m = Submodule.span ℂ (WmSet m) := rfl

lemma WmSet_finite (m : Fin 8 → ℕ) : (WmSet m).Finite := by
  refine Set.Finite.subset
    (Set.Finite.image (fun w : List (Fin 8) => (Submodule.Quotient.mk (wordElt w) : V))
      (Commons.Data.List.finite_setOf_count_eq m)) ?_
  rintro x ⟨w, hw, rfl⟩
  exact ⟨w, hw, rfl⟩

/-- **The word space `Wm m` is finite-dimensional.** -/
theorem Wm_finite (m : Fin 8 → ℕ) : Module.Finite ℂ ↥(Wm m) := by
  rw [Wm_eq_span_WmSet]
  exact Module.Finite.span_of_finite ℂ (WmSet_finite m)

/-! ## The image of the word spaces in the quotient `L = V ⧸ N` -/

/-- The quotient map `V →ₗ[ℂ] V ⧸ N`. -/
def mkQc (N : Submodule U V) : V →ₗ[ℂ] (V ⧸ N) :=
  LinearMap.restrictScalars ℂ (Submodule.mkQ N)

@[simp] lemma mkQc_apply (N : Submodule U V) (x : V) : mkQc N x = Submodule.mkQ N x := rfl

/-- The image of the word space `Wm m` in `L = V ⧸ N`: the weight space of weight `wt m`. -/
def Lw (N : Submodule U V) (m : Fin 8 → ℕ) : Submodule ℂ (V ⧸ N) :=
  (Wm m).map (mkQc N)

lemma mem_Lw_iff {N : Submodule U V} {m : Fin 8 → ℕ} {x : V ⧸ N} :
    x ∈ Lw N m ↔ ∃ y ∈ Wm m, mkQc N y = x :=
  Submodule.mem_map

lemma mk_mem_Lw (N : Submodule U V) (w : List (Fin 8)) :
    mkQc N (Submodule.Quotient.mk (wordElt w) : V) ∈ Lw N (fun i => w.count i) :=
  Submodule.mem_map.mpr ⟨_, mk_wordElt_mem_Wm w, rfl⟩

lemma iSup_Lw_eq_top (N : Submodule U V) : (⨆ m : Fin 8 → ℕ, Lw N m) = ⊤ := by
  simp only [Lw]
  rw [← Submodule.map_iSup, iSup_Wm_eq_top, Submodule.map_top]
  refine LinearMap.range_eq_top.mpr fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | _ y => exact ⟨y, rfl⟩

/-- The surjection `Wm m → Lw m`. -/
def toLw (N : Submodule U V) (m : Fin 8 → ℕ) : ↥(Wm m) →ₗ[ℂ] ↥(Lw N m) where
  toFun y := ⟨mkQc N y, Submodule.mem_map.mpr ⟨y, y.2, rfl⟩⟩
  map_add' x y := by ext; simp [map_add]
  map_smul' c x := by ext; simp [map_smul]

lemma toLw_surjective (N : Submodule U V) (m : Fin 8 → ℕ) :
    Function.Surjective (toLw N m) := by
  intro x
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp x.2
  refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
  show mkQc N y = ↑x
  exact hyx

/-- **The weight spaces of `L = V ⧸ N` are finite-dimensional.** -/
theorem Lw_finite (N : Submodule U V) (m : Fin 8 → ℕ) : Module.Finite ℂ ↥(Lw N m) := by
  haveI := Wm_finite m
  exact Module.Finite.of_surjective (toLw N m) (toLw_surjective N m)

/-! ## The action of `U(e₈)` on the quotient, and the scalar action of the Cartan -/

/-- The ℂ-linear endomorphism of `L = V ⧸ N` attached to `u : U(e₈)`. -/
def endU (N : Submodule U V) (u : U) : Module.End ℂ (V ⧸ N) where
  toFun x := u • x
  map_add' x y := smul_add u x y
  map_smul' c x := Submission.Enveloping.module_smul_comm_scalar (R := ℂ)
    (L := LieAlgebra.e₈ ℂ) u c x

@[simp] lemma endU_apply (N : Submodule U V) (u : U) (x : V ⧸ N) :
    endU N u x = u • x := rfl

lemma endU_mul (N : Submodule U V) (u u' : U) :
    endU N (u * u') = endU N u * endU N u' := by
  ext x; simp [mul_smul]

lemma endU_add (N : Submodule U V) (u u' : U) :
    endU N (u + u') = endU N u + endU N u' := by
  ext x; simp [add_smul]

lemma endU_sub (N : Submodule U V) (u u' : U) :
    endU N (u - u') = endU N u - endU N u' := by
  ext x; simp [sub_smul]

lemma mkQc_smul (N : Submodule U V) (i : Fin 8) (y : V) :
    (Submission.E8Weights.h i) • (mkQc N y) = mkQc N ((Submission.E8Weights.h i) • y) := by
  simp only [mkQc, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_smul]

/-- The scalar action of `Hᵢ` on the weight space `Lw m`. -/
lemma endU_h_apply_mem_Lw (N : Submodule U V) (i : Fin 8) (m : Fin 8 → ℕ) {x : V ⧸ N}
    (hx : x ∈ Lw N m) :
    endU N (Submission.E8Weights.h i) x = (wt m i) • x := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  rw [endU_apply, mkQc_smul, h_smul_eq i y, Hbar_apply_mem_Wm i hy]
  simp only [mkQc, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_smul]

/-! ## The killer projection onto a single weight space of `L` -/

/-- The descended killer: it annihilates the weight space of weight `wt m` and fixes that of
weight `wt m₀`. -/
def killerL (N : Submodule U V) (m₀ m : Fin 8 → ℕ) (j : Fin 8) : Module.End ℂ (V ⧸ N) :=
  ((wt m₀ j - wt m j)⁻¹) •
    (endU N (Submission.E8Weights.h j) - (wt m j) • (1 : Module.End ℂ (V ⧸ N)))

lemma killerL_apply_mem_Lw (N : Submodule U V) (m₀ m n : Fin 8 → ℕ) (j : Fin 8) {x : V ⧸ N}
    (hx : x ∈ Lw N n) :
    killerL N m₀ m j x = ((wt m₀ j - wt m j)⁻¹ * (wt n j - wt m j)) • x := by
  rw [killerL, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, endU_h_apply_mem_Lw N j n hx]
  rw [← sub_smul, smul_smul]

lemma killerL_mem_Lw (N : Submodule U V) (m₀ m : Fin 8 → ℕ) (j : Fin 8) (n : Fin 8 → ℕ)
    {x : V ⧸ N} (hx : x ∈ Lw N n) : killerL N m₀ m j x ∈ Lw N n := by
  rw [killerL_apply_mem_Lw N m₀ m n j hx]
  exact Submodule.smul_mem _ _ hx

/-- A product of killers acts on the weight space `Lw n` by the product of the scalars. -/
lemma prod_killerL_apply (N : Submodule U V) (m₀ : Fin 8 → ℕ) (j : (Fin 8 → ℕ) → Fin 8)
    (l : List (Fin 8 → ℕ)) (n : Fin 8 → ℕ) {x : V ⧸ N} (hx : x ∈ Lw N n) :
    (l.map (fun m => killerL N m₀ m (j m))).prod x
      = (l.map (fun m => (wt m₀ (j m) - wt m (j m))⁻¹ * (wt n (j m) - wt m (j m)))).prod • x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
        map_smul, killerL_apply_mem_Lw N m₀ a n (j a) hx, smul_smul]
      congr 1
      ring

/-- **Uniqueness of the weight decomposition of `L = V ⧸ N`.** -/
theorem eq_zero_of_sum_eq_zero (N : Submodule U V) {s : Finset (Fin 8 → ℕ)}
    {y : (Fin 8 → ℕ) → V ⧸ N} (hy : ∀ m ∈ s, y m ∈ Lw N m)
    (hsum : ∑ m ∈ s, y m = 0) : ∀ m ∈ s, y m = 0 := by
  classical
  intro m₀ hm₀
  have hjex : ∀ m : Fin 8 → ℕ, ∃ j : Fin 8, m = m₀ ∨ wt m j ≠ wt m₀ j := by
    intro m
    by_cases h : m = m₀
    · exact ⟨0, Or.inl h⟩
    · have hne : wt m ≠ wt m₀ := fun hh => h (wt_injective hh)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      exact ⟨j, Or.inr hj⟩
  choose j hj using hjex
  set l : List (Fin 8 → ℕ) := (s.erase m₀).toList with hl
  have hmem : ∀ m ∈ s.erase m₀, m ∈ l := fun m hm => Finset.mem_toList.mpr hm
  have hzero : ∀ m ∈ s, m ≠ m₀ →
      ((l.map (fun m' => killerL N m₀ m' (j m'))).prod) (y m) = 0 := by
    intro m hm hne
    rw [prod_killerL_apply N m₀ j l m (hy m hm)]
    have hfac : ((wt m₀ (j m) - wt m (j m))⁻¹ * (wt m (j m) - wt m (j m))) = 0 := by
      rw [sub_self, mul_zero]
    have h0 : (0 : ℂ) ∈ l.map (fun m' =>
        (wt m₀ (j m') - wt m' (j m'))⁻¹ * (wt m (j m') - wt m' (j m'))) :=
      List.mem_map.mpr ⟨m, hmem m (Finset.mem_erase.mpr ⟨hne, hm⟩), hfac⟩
    rw [List.prod_eq_zero h0, zero_smul]
  have h1 : ((l.map (fun m' => killerL N m₀ m' (j m'))).prod) (∑ m ∈ s, y m) = y m₀ := by
    rw [map_sum, Finset.sum_eq_single m₀ hzero (fun h => absurd hm₀ h)]
    rw [prod_killerL_apply N m₀ j l m₀ (hy m₀ hm₀)]
    have hone : (l.map (fun m =>
        (wt m₀ (j m) - wt m (j m))⁻¹ * (wt m₀ (j m) - wt m (j m)))).prod = 1 := by
      refine List.prod_eq_one fun z hz => ?_
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
      have hm' : m ∈ s.erase m₀ := Finset.mem_toList.mp hm
      have hne := (hj m).resolve_left (Finset.ne_of_mem_erase hm')
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm)
    rw [hone, one_smul]
  rw [hsum, map_zero] at h1
  exact h1.symm

open Submission.E8PBW (fmono)

lemma count_cons_apply (a : Fin 8) (t : List (Fin 8)) (k : Fin 8) :
    (a :: t).count k = t.count k + (if k = a then 1 else 0) := by
  rw [List.count_cons]
  by_cases h : k = a
  · subst h; simp
  · rw [if_neg h]
    rw [if_neg (fun hb => h (beq_iff_eq.mp hb).symm)]

lemma fmono_singleton (i : Fin 8) : fmono [i] = Submission.E8Weights.f i := by
  simp [Submission.E8PBW.fmono]

/-- `fᵢ` maps the weight space of `Wm m` into the weight space of `m + eᵢ`. -/
lemma Lbar_mem_Wm (i : Fin 8) {m : Fin 8 → ℕ} {x : V} (hx : x ∈ Wm m) :
    Lbar E8 i x ∈ Wm (Function.update m i (m i + 1)) := by
  have h1 : Lbar E8 i x = fmono [i] • x := by
    rw [fmono_singleton]
    exact (f_smul_eq i x).symm
  rw [h1]
  have hidx : (fun k => m k + ([i] : List (Fin 8)).count k) = Function.update m i (m i + 1) := by
    funext k
    rw [Function.update_apply, List.count_singleton]
    by_cases h : k = i
    · subst h; simp [beq_iff_eq]
    · rw [if_neg h]
      rw [if_neg (fun hb => h (beq_iff_eq.mp hb).symm)]
      simp
  have h2 := Submission.E8NullVector.fmono_smul_mem_Wm [i] hx
  rwa [hidx] at h2

end Submission.E8WeightSpaces

namespace Submission.E8WeightSpaces

open Submission.StarModule (wordElt wordElt_nil bas bas_apply Lop Lop_wordElt Eword wrho
  Eop_apply)
open Submission.StarQuotient (Hbar Ebar Lbar J V Hbar_mk Ebar_mk Lbar_mk)
open Submission.VermaWeight
open Submission.E8NullVector (f_smul_eq e_smul_eq h_smul_eq)

abbrev E8'' : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

/-! ## The joint Cartan eigenspaces, indexed by integral weights -/

/-- The joint eigenspace of the Cartan generators at the integral weight `μ`. -/
def Lwt (N : Submodule U V) (μ : Fin 8 → ℤ) : Submodule ℂ (V ⧸ N) :=
  ⨅ i : Fin 8, Module.End.eigenspace (endU N (Submission.E8Weights.h i)) ((μ i : ℤ) : ℂ)

lemma mem_Lwt_iff {N : Submodule U V} {μ : Fin 8 → ℤ} {x : V ⧸ N} :
    x ∈ Lwt N μ ↔ ∀ i, endU N (Submission.E8Weights.h i) x = ((μ i : ℤ) : ℂ) • x := by
  simp only [Lwt, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

lemma Lw_le_Lwt (N : Submodule U V) (m : Fin 8 → ℕ) : Lw N m ≤ Lwt N (wtZ m) := by
  intro x hx
  rw [mem_Lwt_iff]
  intro i
  rw [endU_h_apply_mem_Lw N i m hx, wt_eq_cast]

open Submission.E8Weights in
/-- The weight of `eⱼ x` for `x` of weight `μ`: `μ + (Aᵢⱼ)ᵢ`. -/
lemma endU_e_apply_mem_Lwt (N : Submodule Submission.VermaWeight.U V) (j : Fin 8) {μ : Fin 8 → ℤ} {x : V ⧸ N}
    (hx : x ∈ Lwt N μ) :
    endU N (Submission.E8Weights.e j) x ∈ Lwt N (fun i => μ i + E8 i j) := by
  rw [mem_Lwt_iff] at hx ⊢
  intro i
  have hx' : Submission.E8Weights.h i • x = ((μ i : ℤ) : ℂ) • x := by
    simpa only [endU_apply] using hx i
  have hrel : Submission.E8Weights.h i * Submission.E8Weights.e j
      = Submission.E8Weights.e j * Submission.E8Weights.h i
        + ((E8 i j : ℤ) : ℂ) • Submission.E8Weights.e j := by
    have h := Submission.E8Weights.commutator_H_E i j
    change UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i)
        * UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE j)
      = UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE j)
        * UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i)
        + ((E8 i j : ℤ) : ℂ) • UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE j)
    rw [← Int.cast_smul_eq_zsmul ℂ (E8 i j)
      (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreE j))] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [endU_apply, endU_apply]
  rw [show Submission.E8Weights.h i • (Submission.E8Weights.e j • x)
      = Submission.E8Weights.h i • (Submission.E8Weights.e j • x) from rfl]
  trans (Submission.E8Weights.h i * Submission.E8Weights.e j) • x
  · rw [mul_smul]
  · rw [hrel, add_smul, mul_smul, smul_assoc, hx',
      Submission.Enveloping.module_smul_comm_scalar (R := ℂ) (L := LieAlgebra.e₈ ℂ)
        (Submission.E8Weights.e j) ((μ i : ℤ) : ℂ) x,
      ← add_smul]
    congr 1
    push_cast
    ring

open Submission.E8Weights in
/-- The weight of `fⱼ x` for `x` of weight `μ`: `μ - (Aᵢⱼ)ᵢ`. -/
lemma endU_f_apply_mem_Lwt (N : Submodule Submission.VermaWeight.U V) (j : Fin 8) {μ : Fin 8 → ℤ} {x : V ⧸ N}
    (hx : x ∈ Lwt N μ) :
    endU N (Submission.E8Weights.f j) x ∈ Lwt N (fun i => μ i - E8 i j) := by
  rw [mem_Lwt_iff] at hx ⊢
  intro i
  have hx' : Submission.E8Weights.h i • x = ((μ i : ℤ) : ℂ) • x := by
    simpa only [endU_apply] using hx i
  have hrel : Submission.E8Weights.h i * Submission.E8Weights.f j
      = Submission.E8Weights.f j * Submission.E8Weights.h i
        + ((-(E8 i j) : ℤ) : ℂ) • Submission.E8Weights.f j := by
    have h := Submission.E8Weights.commutator_H_F i j
    change UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i)
        * UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF j)
      = UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF j)
        * UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreH i)
        + ((-(E8 i j) : ℤ) : ℂ) • UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF j)
    rw [← Int.cast_smul_eq_zsmul ℂ (-(E8 i j))
      (UniversalEnvelopingAlgebra.ι ℂ (Submission.E8Weights.SerreF j))] at h
    rw [sub_eq_iff_eq_add] at h
    rw [h, add_comm]
  rw [endU_apply, endU_apply]
  trans (Submission.E8Weights.h i * Submission.E8Weights.f j) • x
  · rw [mul_smul]
  · rw [hrel, add_smul, mul_smul, smul_assoc, hx',
      Submission.Enveloping.module_smul_comm_scalar (R := ℂ) (L := LieAlgebra.e₈ ℂ)
        (Submission.E8Weights.f j) ((μ i : ℤ) : ℂ) x,
      ← add_smul]
    congr 1
    push_cast
    ring

/-! ## The killer projection and the identification `Lw m = Lwt (wtZ m)` -/

lemma killerL_apply_mem_Lwt (N : Submodule U V) (m₀ m : Fin 8 → ℕ) (j : Fin 8) {x : V ⧸ N}
    (hx : x ∈ Lwt N (wtZ m₀)) :
    killerL N m₀ m j x = ((wt m₀ j - wt m j)⁻¹ * (wt m₀ j - wt m j)) • x := by
  rw [killerL, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [show endU N (Submission.E8Weights.h j) x = (wt m₀ j) • x from ?_]
  · rw [← sub_smul, smul_smul]
  · rw [mem_Lwt_iff] at hx
    rw [hx j, wt_eq_cast]

lemma prod_killerL_apply_Lwt (N : Submodule U V) (m₀ : Fin 8 → ℕ) (j : (Fin 8 → ℕ) → Fin 8)
    (l : List (Fin 8 → ℕ)) {x : V ⧸ N} (hx : x ∈ Lwt N (wtZ m₀)) :
    (l.map (fun m => killerL N m₀ m (j m))).prod x
      = (l.map (fun m => (wt m₀ (j m) - wt m (j m))⁻¹ * (wt m₀ (j m) - wt m (j m)))).prod • x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
        map_smul, killerL_apply_mem_Lwt N m₀ a (j a) hx, smul_smul]
      congr 1
      ring

/-- Every element of `L = V ⧸ N` is a finite sum of weight components. -/
lemma exists_decomp_Lw (N : Submodule U V) (x : V ⧸ N) :
    ∃ (s : Finset (Fin 8 → ℕ)) (y : (Fin 8 → ℕ) → V ⧸ N),
      (∀ m ∈ s, y m ∈ Lw N m) ∧ x = ∑ m ∈ s, y m := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective N x
  obtain ⟨s, y, hy, hsum⟩ := Submission.VermaWeight.exists_decomp z
  refine ⟨s, fun m => mkQc N (y m), fun m hm => Submodule.mem_map.mpr ⟨_, hy m hm, rfl⟩, ?_⟩
  show Submodule.mkQ N z = ∑ m ∈ s, mkQc N (y m)
  rw [hsum, map_sum]
  simp

/-- The "projection" onto the weight space `Lw m` inside `L`: a product of killers which fixes
`Lw m` and `Lwt (wtZ m)` and kills the other components of a decomposition along finitely many
weight spaces. -/
theorem Lw_eq_Lwt (N : Submodule U V) (m : Fin 8 → ℕ) : Lw N m = Lwt N (wtZ m) := by
  classical
  refine le_antisymm (Lw_le_Lwt N m) ?_
  intro x hx
  obtain ⟨s, y, hy, hsum⟩ := exists_decomp_Lw N x
  have hjex : ∀ m' : Fin 8 → ℕ, ∃ j : Fin 8, m' = m ∨ wt m' j ≠ wt m j := by
    intro m'
    by_cases h : m' = m
    · exact ⟨0, Or.inl h⟩
    · have hne : wt m' ≠ wt m := fun hh => h (wt_injective hh)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      exact ⟨j, Or.inr hj⟩
  choose j hj using hjex
  have hj' : ∀ m' ∈ s, m' ≠ m → wt m' (j m') ≠ wt m (j m') :=
    fun m' _ hne => (hj m').resolve_left hne
  set l : List (Fin 8 → ℕ) := (s.erase m).toList with hl
  have hmem : ∀ m' ∈ s.erase m, m' ∈ l := fun m' hm' => Finset.mem_toList.mpr hm'
  set P : Module.End ℂ (V ⧸ N) := (l.map (fun m' => killerL N m m' (j m'))).prod with hP
  have hone : (l.map (fun m' =>
      (wt m (j m') - wt m' (j m'))⁻¹ * (wt m (j m') - wt m' (j m')))).prod = 1 := by
    refine List.prod_eq_one fun z hz => ?_
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hz
    have hm'' : m' ∈ s.erase m := Finset.mem_toList.mp hm'
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm (hj' m' (Finset.mem_of_mem_erase hm'')
      (Finset.ne_of_mem_erase hm''))))
  have hPx : P x = x := by
    rw [hP, prod_killerL_apply_Lwt N m j l hx, hone, one_smul]
  have hP0 : ∀ m' ∈ s.erase m, P (y m') = 0 := by
    intro m' hm'
    rw [hP, prod_killerL_apply N m j l m' (hy m' (Finset.mem_of_mem_erase hm'))]
    have hfac : ((wt m (j m') - wt m' (j m'))⁻¹ * (wt m' (j m') - wt m' (j m'))) = 0 := by
      rw [sub_self, mul_zero]
    have hmen : (0 : ℂ) ∈ l.map (fun m'' =>
        (wt m (j m'') - wt m'' (j m''))⁻¹ * (wt m' (j m'') - wt m'' (j m''))) :=
      List.mem_map.mpr ⟨m', hmem m' hm', hfac⟩
    rw [List.prod_eq_zero hmen, zero_smul]
  have hsumP : P (∑ m' ∈ s, y m') = (if m ∈ s then y m else 0) := by
    rw [map_sum]
    by_cases hm : m ∈ s
    · rw [if_pos hm,
        Finset.sum_eq_single m (fun m' hm' hne => hP0 m' (Finset.mem_erase.mpr ⟨hne, hm'⟩))
          (fun h => absurd hm h)]
      rw [hP, prod_killerL_apply N m j l m (hy m hm), hone, one_smul]
    · rw [if_neg hm]
      refine Finset.sum_eq_zero fun m' hm' => ?_
      exact hP0 m' (Finset.mem_erase.mpr ⟨fun h => hm (h ▸ hm'), hm'⟩)
  rw [← hsum] at hsumP
  rw [hPx] at hsumP
  by_cases hm : m ∈ s
  · rw [if_pos hm] at hsumP
    rw [hsumP]
    exact hy m hm
  · rw [if_neg hm] at hsumP
    rw [hsumP]
    exact Submodule.zero_mem _

end Submission.E8WeightSpaces

namespace Submission.E8WeightSpaces

open Submission.StarModule (wordElt wordElt_nil bas bas_apply Lop Lop_wordElt Eword wrho
  Eop_apply)
open Submission.StarQuotient (Hbar Ebar Lbar J V Hbar_mk Ebar_mk Lbar_mk)
open Submission.VermaWeight
open Submission.E8NullVector (f_smul_eq e_smul_eq h_smul_eq)

abbrev E8''' : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

/-! ## Finiteness, spanning, and the support of the weight spaces -/

/-- The weight spaces are finite-dimensional. -/
theorem Lwt_finite (N : Submodule U V) (m : Fin 8 → ℕ) :
    Module.Finite ℂ ↥(Lwt N (wtZ m)) := by
  rw [← Lw_eq_Lwt]
  exact Lw_finite N m

/-- The weight spaces span `L = V ⧸ N`. -/
lemma iSup_Lwt_eq_top (N : Submodule U V) : (⨆ μ : Fin 8 → ℤ, Lwt N μ) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← iSup_Lw_eq_top N]
  refine iSup_le fun m => ?_
  rw [Lw_eq_Lwt]
  exact le_iSup (fun μ : Fin 8 → ℤ => Lwt N μ) (wtZ m)

/-- Two weight spaces with non-zero intersection have the same weight: a non-zero vector cannot be
an eigenvector for two different eigenvalues of the same operator. -/
lemma eq_of_mem_Lwt_of_mem_Lwt (N : Submodule U V) {μ μ' : Fin 8 → ℤ} {x : V ⧸ N}
    (hx : x ∈ Lwt N μ) (hx' : x ∈ Lwt N μ') (hx0 : x ≠ 0) : μ = μ' := by
  funext i
  rw [mem_Lwt_iff] at hx hx'
  have h2 : ((((μ i : ℤ) : ℂ)) - (((μ' i : ℤ) : ℂ))) • x = 0 := by
    rw [sub_smul, ← hx i, ← hx' i, sub_self]
  have h3 : (((μ i : ℤ) : ℂ)) = (((μ' i : ℤ) : ℂ)) :=
    sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx0)
  exact_mod_cast h3

/-- The scalar by which a killer acts on the joint eigenspace of weight `μ`. -/
lemma killerL_apply_mem_Lwt' (N : Submodule U V) (m₀ m : Fin 8 → ℕ) (j : Fin 8)
    {μ : Fin 8 → ℤ} {x : V ⧸ N} (hx : x ∈ Lwt N μ) :
    killerL N m₀ m j x = ((wt m₀ j - wt m j)⁻¹ * (((μ j : ℤ) : ℂ) - wt m j)) • x := by
  rw [killerL, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [show endU N (Submission.E8Weights.h j) x = (((μ j : ℤ) : ℂ)) • x from ?_]
  · rw [← sub_smul, smul_smul]
  · rw [mem_Lwt_iff] at hx
    exact hx j

/-- A product of killers acts on the joint eigenspace of weight `μ` by the product of scalars. -/
lemma prod_killerL_apply_Lwt' (N : Submodule U V) (m₀ : Fin 8 → ℕ) (j : (Fin 8 → ℕ) → Fin 8)
    (l : List (Fin 8 → ℕ)) {μ : Fin 8 → ℤ} {x : V ⧸ N} (hx : x ∈ Lwt N μ) :
    (l.map (fun m => killerL N m₀ m (j m))).prod x
      = (l.map (fun m => (wt m₀ (j m) - wt m (j m))⁻¹ *
          (((μ (j m) : ℤ) : ℂ) - wt m (j m)))).prod • x := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply, ih,
        map_smul, killerL_apply_mem_Lwt' N m₀ a (j a) hx, smul_smul]
      congr 1
      ring

/-- **The support of `L = V ⧸ N` is contained in `λ - ℕΦ⁺` (in integral form):** every non-zero
weight vector has a weight of the form `wtZ m`. -/
theorem exists_wtZ_of_mem_Lwt (N : Submodule U V) {μ : Fin 8 → ℤ} {x : V ⧸ N}
    (hx : x ∈ Lwt N μ) (hx0 : x ≠ 0) : ∃ m : Fin 8 → ℕ, μ = wtZ m := by
  classical
  obtain ⟨s, y, hy, hsum⟩ := exists_decomp_Lw N x
  -- some component is non-zero
  obtain ⟨m₀, hm₀, hm₀0⟩ : ∃ m ∈ s, y m ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx0 (by rw [hsum]; exact Finset.sum_eq_zero hcon)
  -- the killer projection onto the `m₀`-component
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
  set l : List (Fin 8 → ℕ) := (s.erase m₀).toList with hl
  have hmem : ∀ m ∈ s.erase m₀, m ∈ l := fun m hm => Finset.mem_toList.mpr hm
  set P : Module.End ℂ (V ⧸ N) := (l.map (fun m => killerL N m₀ m (j m))).prod with hP
  have hfix : (l.map (fun m => (wt m₀ (j m) - wt m (j m))⁻¹ * (wt m₀ (j m) - wt m (j m)))).prod
      = 1 := by
    refine List.prod_eq_one fun z hz => ?_
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hz
    have hm' : m ∈ s.erase m₀ := Finset.mem_toList.mp hm
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm (hj' m (Finset.mem_of_mem_erase hm')
      (Finset.ne_of_mem_erase hm'))))
  have hPy : P (y m₀) = y m₀ := by
    rw [hP, prod_killerL_apply N m₀ j l m₀ (hy m₀ hm₀), hfix, one_smul]
  have hP0 : ∀ m ∈ s.erase m₀, P (y m) = 0 := by
    intro m hm
    rw [hP, prod_killerL_apply N m₀ j l m (hy m (Finset.mem_of_mem_erase hm))]
    have hfac : ((wt m₀ (j m) - wt m (j m))⁻¹ * (wt m (j m) - wt m (j m))) = 0 := by
      rw [sub_self, mul_zero]
    have hmen : (0 : ℂ) ∈ l.map (fun m' =>
        (wt m₀ (j m') - wt m' (j m'))⁻¹ * (wt m (j m') - wt m' (j m'))) :=
      List.mem_map.mpr ⟨m, hmem m hm, hfac⟩
    rw [List.prod_eq_zero hmen, zero_smul]
  have hPsum : P x = y m₀ := by
    rw [hsum, map_sum,
      Finset.sum_eq_single m₀ (fun m hm hne => hP0 m (Finset.mem_erase.mpr ⟨hne, hm⟩))
        (fun h => absurd hm₀ h)]
    exact hPy
  -- the same product acts on `x` as a scalar
  rw [hP] at hPsum
  have hscal := prod_killerL_apply_Lwt' N m₀ j l hx
  rw [hscal] at hPsum
  -- hence `x` is a multiple of the weight vector `y m₀` of weight `wtZ m₀`
  rcases eq_or_ne ((l.map (fun m =>
      (wt m₀ (j m) - wt m (j m))⁻¹ * (((μ (j m) : ℤ) : ℂ) - wt m (j m)))).prod) 0 with h0 | h0
  · rw [h0, zero_smul] at hPsum
    exact absurd hPsum.symm hm₀0
  · have hxmem : x ∈ Lwt N (wtZ m₀) := by
      have h1 : x = ((l.map (fun m => (wt m₀ (j m) - wt m (j m))⁻¹ *
          (((μ (j m) : ℤ) : ℂ) - wt m (j m)))).prod)⁻¹ • y m₀ := by
        rw [← hPsum, smul_smul, inv_mul_cancel₀ h0, one_smul]
      rw [h1]
      exact Submodule.smul_mem _ _ (Lw_le_Lwt N m₀ (hy m₀ hm₀))
    exact ⟨m₀, eq_of_mem_Lwt_of_mem_Lwt N hx hxmem hx0⟩

end Submission.E8WeightSpaces

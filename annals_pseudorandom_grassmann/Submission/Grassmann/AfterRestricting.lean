import Submission.Grassmann.BoundsComposition

/-!
# `lem:after restricting` of arXiv:2209.04243 §8

Combining `lem:bounds on composition` with `lem:hyp inductive step`, and reindexing the
quintuples `(V₁,W₁,V₂,W₂,X)` by the triples `(V₂,W₂,X)` (the triple determines
`V₁ = Q_{V₂}⁻¹(Im X)` and `W₁ = ker X`), one obtains that a function of degree at most `d`
satisfies

  `(1/162)‖f‖₄⁴ ≤ q^{6d²}‖f‖₂⁴
     + Σ_{V₂,W₂,X : |(V₂,W₂,X)|>0} q^{24d|(V₂,W₂,X)|} E_T‖D_X D_{V₂,W₂,T}[f]‖₄⁴`.

This file proves the reindexed form (`after_restricting`).
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## Rank computations -/

/-- Arithmetic: `b - (a + (c - d)) = d - (e + a)` when `e + b = c`, `e + a ≤ d ≤ c`. -/
private lemma sub_sub_order (a b c d e : ℕ) (h1 : e + b = c) (h2 : e + a ≤ d) (h3 : d ≤ c) :
    b - (a + (c - d)) = d - (e + a) := by omega

/-- The kernel of `Y₂ = Y|_{W₂}^{V/V₂}` as a subspace of `W₂` is `Y⁻¹(V₂) ⊓ W₂`. -/
theorem ker_YlinOf (V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    LinearMap.ker (YlinOf V₂ W₂ Y) =
      Submodule.comap W₂.subtype (Submodule.comap Y.mulVecLin V₂) := by
  ext w
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_comap]
  constructor
  · intro h
    have h2 : Submodule.mkQ V₂ (Y.mulVecLin w.1) = 0 := h
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  · intro h
    change Submodule.mkQ V₂ (Y.mulVecLin w.1) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h

/-- **The rank of `Y₂ = Y|_{W₂}^{V/V₂}`** under the hybrid condition:
`rank Y₂ = rank Y - |(V₂,W₂)|`. -/
theorem finrank_range_YlinOf {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {Y : Matrix (Fin n) (Fin m) 𝔽₂} (h : hybridPredSub V₂ W₂ Y) :
    Module.finrank 𝔽₂ (LinearMap.range (YlinOf V₂ W₂ Y)) =
      Y.rank - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)) := by
  set A := Submodule.comap Y.mulVecLin V₂ with hA
  have hker : LinearMap.ker (YlinOf V₂ W₂ Y) = Submodule.comap W₂.subtype A :=
    ker_YlinOf V₂ W₂ Y
  have hfin : Module.finrank 𝔽₂ ↥(Submodule.comap W₂.subtype A) = Module.finrank 𝔽₂ ↥A :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe h.2)
  have hrank : Module.finrank 𝔽₂ (LinearMap.range (YlinOf V₂ W₂ Y)) =
      Module.finrank 𝔽₂ ↥W₂ - Module.finrank 𝔽₂ ↥(LinearMap.ker (YlinOf V₂ W₂ Y)) := by
    have := LinearMap.finrank_range_add_finrank_ker (YlinOf V₂ W₂ Y)
    omega
  have hcomap : Module.finrank 𝔽₂ ↥A =
      Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin) + Module.finrank 𝔽₂ V₂ := by
    have := Commons.LinearAlgebra.finrank_comap_eq Y.mulVecLin V₂
    rw [← hA, inf_eq_left.mpr h.1] at this
    omega
  have hYker : Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin) + Y.rank = m := by
    have := LinearMap.finrank_range_add_finrank_ker Y.mulVecLin
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at this
    have hr : Y.rank = Module.finrank 𝔽₂ (LinearMap.range Y.mulVecLin) := rfl
    rw [hr]; omega
  have hAle : Module.finrank 𝔽₂ ↥A ≤ Module.finrank 𝔽₂ ↥W₂ := Submodule.finrank_mono h.2
  have hW₂le : Module.finrank 𝔽₂ ↥W₂ ≤ m := by
    have hh := Submodule.finrank_le W₂
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at hh
    exact hh
  rw [hrank, hker, hfin, hcomap]
  have h4 : Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin) + Module.finrank 𝔽₂ ↥V₂
      ≤ Module.finrank 𝔽₂ ↥W₂ := by rw [← hcomap]; exact hAle
  exact (sub_sub_order (Module.finrank 𝔽₂ ↥V₂) Y.rank m (Module.finrank 𝔽₂ ↥W₂)
    (Module.finrank 𝔽₂ ↥(LinearMap.ker Y.mulVecLin)) hYker h4 hW₂le).symm

/-- If `X ≤ Y₂` in the rank order then `rank X + |(V₂,W₂)| ≤ rank Y`. -/
theorem rank_add_order_le_of_lmLE {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)}
    {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)} {Y : Matrix (Fin n) (Fin m) 𝔽₂}
    (h : hybridPredSub V₂ W₂ Y) {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)}
    (hX : lmLE X (YlinOf V₂ W₂ Y)) :
    Module.finrank 𝔽₂ (LinearMap.range X) +
        (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)) ≤ Y.rank := by
  have h1 := (lmLE_iff X (YlinOf V₂ W₂ Y)).mp hX
  have hle : Module.finrank 𝔽₂ (LinearMap.range X) ≤
      Module.finrank 𝔽₂ (LinearMap.range (YlinOf V₂ W₂ Y)) :=
    Submodule.finrank_mono h1.1
  rw [finrank_range_YlinOf h] at hle
  have hord := hybridPredSub_order_le_rank V₂ W₂ Y h
  omega

/-! ## The order cut-off for the derivatives -/

/-- **The `X`-derivative of a restricted hybrid Laplacian vanishes past the degree**: if
`d < |(V₂,W₂)| + rank X` and `DegLe d f` then
`D_X (D_{V₂,W₂,T}[f]) = 0`. -/
theorem lapMulN_plLE_restr_eq_zero {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)} (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (h : d < Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) +
      Module.finrank 𝔽₂ (LinearMap.range X)) :
    lapMulN (plLE (XtOf V₂ W₂ X)) (restr (Qp V₂) (Ip W₂) (shift T (Lsub V₂ W₂ f))) = 0 := by
  by_cases hA : Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) ≤ d
  · have he : DegLe (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)))
        (restr (Qp V₂) (Ip W₂) (shift T (Lsub V₂ W₂ f))) := by
      change DegLe (d - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)))
        (restr (Qp V₂) (Ip W₂) (shift T (lapMulN (hybridPredSub V₂ W₂) f)))
      refine degLe_restr_shift_lapMulN (Qp V₂) (Ip W₂) T (hybridPredSub V₂ W₂) hf
        (k := Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)) ?_
      intro Y hY
      have h1 : (Qp V₂ * Y * Ip W₂).rank =
          Y.rank - (Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂)) := by
        rw [← charMat, charMat_eq_XtOf, rank_XtOf]
        exact finrank_range_YlinOf hY
      exact le_of_eq h1
    refine eq_of_fcoeff_eq (fun Z => ?_)
    rw [fcoeff_lapMulN, fcoeff_zero]
    by_cases hZ : plLE (XtOf V₂ W₂ X) Z
    · rw [if_pos hZ, one_mul]
      have h1 : (XtOf V₂ W₂ X).rank ≤ Z.rank := plLE_rank_le hZ
      rw [rank_XtOf] at h1
      exact fcoeff_eq_zero_of_rank_gt he (by omega)
    · rw [if_neg hZ, zero_mul]
  · have hz : Lsub V₂ W₂ f = 0 := Lsub_eq_zero_of_lt_order hf V₂ W₂ (by omega)
    rw [hz, shift_zero, restr_zero]
    refine eq_of_fcoeff_eq (fun Z => ?_)
    rw [fcoeff_lapMulN, fcoeff_zero]
    by_cases hZ : plLE (XtOf V₂ W₂ X) Z <;> simp [hZ]

/-- The summand `D_X ∘ D_{V₂,W₂,T}` vanishes past the degree of `f`. -/
theorem DopX_eq_zero_of_degLe {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    {V₂ : Submodule 𝔽₂ (Fin n → 𝔽₂)} {W₂ : Submodule 𝔽₂ (Fin m → 𝔽₂)}
    {X : ↥W₂ →ₗ[𝔽₂] ((Fin n → 𝔽₂) ⧸ V₂)} (T : Matrix (Fin m) (Fin n) 𝔽₂)
    (h : d < Module.finrank 𝔽₂ V₂ + (m - Module.finrank 𝔽₂ W₂) +
      Module.finrank 𝔽₂ (LinearMap.range X)) :
    DopX V₁ W₁ V₂ W₂ X T f = 0 := by
  rw [DopX, lapMulN_plLE_restr_eq_zero hf T h, restr_zero]

/-! ## The section `t ↦ (V₁,W₁)` of the index set -/

/-- The `V₁` determined by a triple `(V₂,W₂,X)`: the preimage of `Im X` under `V → V/V₂`. -/
noncomputable def trV₁ (t : Triple m n) : Submodule 𝔽₂ (Fin n → 𝔽₂) :=
  Submodule.comap (Submodule.mkQ t.1) (LinearMap.range t.2.2)

/-- The `W₁` determined by a triple `(V₂,W₂,X)`: the kernel of `X`, viewed inside `W`. -/
noncomputable def trW₁ (t : Triple m n) : Submodule 𝔽₂ (Fin m → 𝔽₂) :=
  Submodule.map t.2.1.subtype (LinearMap.ker t.2.2)

/-- The total order `|(V₂,W₂,X)| = dim V₂ + codim W₂ + rank X` of a triple. -/
noncomputable def totOrder (t : Triple m n) : ℕ :=
  Module.finrank 𝔽₂ t.1 + (m - Module.finrank 𝔽₂ t.2.1) +
    Module.finrank 𝔽₂ (LinearMap.range t.2.2)

/-- **A triple is admissible for `(V₁,W₁)` exactly when `(V₁,W₁)` is the section of the
triple.** -/
theorem TripleOK_iff (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂))
    (t : Triple m n) : TripleOK V₁ W₁ t ↔ V₁ = trV₁ t ∧ W₁ = trW₁ t := by
  constructor
  · intro h
    obtain ⟨h1, h2, hker, hrange⟩ := h
    constructor
    · rw [trV₁, hrange, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.mpr h1]
    · rw [trW₁, hker, Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr h2]
  · rintro ⟨hV, hW⟩
    have hV₂V₁ : t.1 ≤ V₁ := by
      rw [hV, trV₁]
      intro x hx
      rw [Submodule.mem_comap]
      have hx0 : Submodule.mkQ t.1 x = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact hx
      rw [hx0]
      exact Submodule.zero_mem _
    have hW₁W₂ : W₁ ≤ t.2.1 := by
      rw [hW, trW₁]
      exact Submodule.map_subtype_le _ _
    refine ⟨hV₂V₁, hW₁W₂, ?_, ?_⟩
    · rw [hW, trW₁, Submodule.comap_map_eq, Submodule.ker_subtype, sup_bot_eq]
    · rw [hV, trV₁, Submodule.map_comap_eq, Submodule.range_mkQ]
      exact (inf_eq_right.mpr le_top).symm

/-- The order of the section of a triple is `|(V₂,W₂,X)| + rank X`. -/
theorem order_section (t : Triple m n) :
    Module.finrank 𝔽₂ (trV₁ t) +
        (m - Module.finrank 𝔽₂ (trW₁ t)) =
      totOrder t + Module.finrank 𝔽₂ (LinearMap.range t.2.2) := by
  have hV : Module.finrank 𝔽₂ (trV₁ t) =
      Module.finrank 𝔽₂ t.1 + Module.finrank 𝔽₂ (LinearMap.range t.2.2) := by
    have h := Commons.LinearAlgebra.finrank_comap_eq (Submodule.mkQ t.1) (LinearMap.range t.2.2)
    rw [Submodule.ker_mkQ] at h
    rw [trV₁, h]
    have h2 : LinearMap.range t.2.2 ⊓ LinearMap.range (Submodule.mkQ t.1) =
        LinearMap.range t.2.2 :=
      inf_eq_left.mpr (le_top.trans (Submodule.range_mkQ t.1).ge)
    rw [h2]
  have hW : Module.finrank 𝔽₂ (trW₁ t) = Module.finrank 𝔽₂ t.2.1 -
      Module.finrank 𝔽₂ (LinearMap.range t.2.2) := by
    have he : Module.finrank 𝔽₂ (trW₁ t) = Module.finrank 𝔽₂ ↥(LinearMap.ker t.2.2) :=
      (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective t.2.1.subtype
        (Submodule.injective_subtype t.2.1) (LinearMap.ker t.2.2))).symm
    have hrn := LinearMap.finrank_range_add_finrank_ker t.2.2
    omega
  have hXle : Module.finrank 𝔽₂ (LinearMap.range t.2.2) ≤ Module.finrank 𝔽₂ t.2.1 := by
    have := LinearMap.finrank_range_add_finrank_ker t.2.2
    omega
  have hW₂le : Module.finrank 𝔽₂ t.2.1 ≤ m := by
    have h := Submodule.finrank_le t.2.1
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at h
    exact h
  rw [hV, hW, totOrder]
  omega

/-- The order of the section of a triple is at most twice the total order of the triple. -/
theorem order_section_le (t : Triple m n) :
    Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t)) ≤ 2 * totOrder t := by
  have h := order_section t
  have h2 : Module.finrank 𝔽₂ (LinearMap.range t.2.2) ≤ totOrder t := by
    rw [totOrder]; omega
  omega

/-! ## `lem:hyp inductive step` in terms of the pairs `(V₁,W₁)` -/

/-- The sum of `lem:hyp inductive step`, reindexed from the dimension pairs `(i,j)` to the
subspace pairs `(V₁,W₁)`. -/
theorem hyp_inductive_step_reindex {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) :
    l4q f ≤ 162 * 2 ^ (6 * d ^ 2) * (l2sq f) ^ 2 +
      2 * ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
          else 2 ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
          l4q (Lup V₁ (Ldown W₁ f)) := by
  have hswap : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
      (if i = 0 ∧ j = 0 then 0 else 2 ^ (7 * d * (i + j))) *
        (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
            l4q (Lup V₁ (Ldown W₁ f)) else 0))) =
      ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
          else 2 ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
          l4q (Lup V₁ (Ldown W₁ f)) := by
    -- push the scalar inside
    have hpush : ∀ i ∈ Finset.range (n + 1), ∀ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else 2 ^ (7 * d * (i + j))) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
              l4q (Lup V₁ (Ldown W₁ f)) else 0)) =
        ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if i = 0 ∧ j = 0 then 0 else 2 ^ (7 * d * (i + j))) *
            (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
              l4q (Lup V₁ (Ldown W₁ f)) else 0) := by
      intro i _ j _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun V₁ _ => ?_)
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun i hi => Finset.sum_congr rfl (fun j hj => hpush i hi j hj))]
    -- reorder: bring `V₁`, `W₁` to the front
    conv_lhs =>
      enter [2, i]
      rw [Finset.sum_comm (s := Finset.range (m + 1))
        (t := (Finset.univ : Finset (Submodule 𝔽₂ (Fin n → 𝔽₂))))
        (f := fun (j : ℕ) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) =>
          ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            ((if i = 0 ∧ j = 0 then (0 : ℝ) else (2 : ℝ) ^ (7 * d * (i + j))) *
              (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
                l4q (Lup V₁ (Ldown W₁ f)) else 0)))]
    conv_lhs =>
      enter [2, i, 2, V₁]
      rw [Finset.sum_comm (s := Finset.range (m + 1))
        (t := (Finset.univ : Finset (Submodule 𝔽₂ (Fin m → 𝔽₂))))
        (f := fun (j : ℕ) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) =>
          ((if i = 0 ∧ j = 0 then (0 : ℝ) else (2 : ℝ) ^ (7 * d * (i + j))) *
            (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
              l4q (Lup V₁ (Ldown W₁ f)) else 0)))]
    conv_lhs =>
      rw [Finset.sum_comm (s := Finset.range (n + 1))
        (t := (Finset.univ : Finset (Submodule 𝔽₂ (Fin n → 𝔽₂))))
        (f := fun (i : ℕ) (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) =>
          ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂), ∑ j ∈ Finset.range (m + 1),
            ((if i = 0 ∧ j = 0 then (0 : ℝ) else (2 : ℝ) ^ (7 * d * (i + j))) *
              (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
                l4q (Lup V₁ (Ldown W₁ f)) else 0)))]
    conv_lhs =>
      enter [2, V₁]
      rw [Finset.sum_comm (s := Finset.range (n + 1))
        (t := (Finset.univ : Finset (Submodule 𝔽₂ (Fin m → 𝔽₂))))
        (f := fun (i : ℕ) (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) =>
          ∑ j ∈ Finset.range (m + 1),
            ((if i = 0 ∧ j = 0 then (0 : ℝ) else (2 : ℝ) ^ (7 * d * (i + j))) *
              (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
                l4q (Lup V₁ (Ldown W₁ f)) else 0)))]
    refine Finset.sum_congr rfl (fun V₁ _ => ?_)
    refine Finset.sum_congr rfl (fun W₁ _ => ?_)
    have hsingle : ∀ i ∈ Finset.range (n + 1), (∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then (0 : ℝ) else (2 : ℝ) ^ (7 * d * (i + j))) *
          (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
            l4q (Lup V₁ (Ldown W₁ f)) else 0)) =
        (if Module.finrank 𝔽₂ V₁ = i then
          (if i = 0 ∧ m - Module.finrank 𝔽₂ W₁ = 0 then (0 : ℝ)
            else (2 : ℝ) ^ (7 * d * (i + (m - Module.finrank 𝔽₂ W₁)))) *
            l4q (Lup V₁ (Ldown W₁ f)) else 0) := by
      intro i _
      have hWle : Module.finrank 𝔽₂ W₁ ≤ m := by
        have h := Submodule.finrank_le W₁
        rw [Module.finrank_fin_fun (R := 𝔽₂)] at h
        exact h
      by_cases hiV : Module.finrank 𝔽₂ V₁ = i
      · rw [if_pos hiV]
        rw [Finset.sum_eq_single (m - Module.finrank 𝔽₂ W₁)]
        · have hW : Module.finrank 𝔽₂ W₁ = m - (m - Module.finrank 𝔽₂ W₁) := by omega
          have h2 : (if Module.finrank 𝔽₂ V₁ = i ∧
              Module.finrank 𝔽₂ W₁ = m - (m - Module.finrank 𝔽₂ W₁) then
              l4q (Lup V₁ (Ldown W₁ f)) else 0) = l4q (Lup V₁ (Ldown W₁ f)) :=
            if_pos ⟨hiV, hW⟩
          rw [h2]
        · intro j hj hji
          have hjle : j ≤ m := by
            have := Finset.mem_range.mp hj
            omega
          have hB : (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
              l4q (Lup V₁ (Ldown W₁ f)) else 0) = 0 := by
            rw [if_neg]
            intro hc
            exact hji (by omega)
          rw [hB, mul_zero]
        · intro hnot
          exact absurd (Finset.mem_range.mpr (by omega)) hnot
      · rw [if_neg hiV]
        refine Finset.sum_eq_zero (fun j _ => ?_)
        have hA : (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j then
            l4q (Lup V₁ (Ldown W₁ f)) else 0) = 0 := by
          rw [if_neg]
          intro hc
          exact hiV hc.1
        rw [hA, mul_zero]
    rw [Finset.sum_congr rfl (fun i hi => hsingle i hi)]
    rw [Finset.sum_eq_single (Module.finrank 𝔽₂ V₁)]
    · rw [if_pos rfl]
      by_cases hzero : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0
      · rw [if_pos hzero, if_pos ⟨by omega, by omega⟩]
      · rw [if_neg hzero, if_neg (fun hc => hzero (by omega))]
    · intro i _ hiV
      rw [if_neg (fun h => hiV h.symm)]
    · intro hnot
      have hle : Module.finrank 𝔽₂ V₁ ≤ n := by
        have h := Submodule.finrank_le V₁
        rw [Module.finrank_fin_fun (R := 𝔽₂)] at h
        exact h
      exact absurd (Finset.mem_range.mpr (by omega)) hnot
  refine le_trans (hyp_inductive_step d f hf) ?_
  rw [hswap]

/-! ## The reindexing of the quintuples by the triples -/

/-- **Reindexing step**: summing over the pairs `(V₁,W₁)` and the admissible triples for them is
the same as summing over all triples, evaluating at the section. -/
theorem reindex_triples (G : (Submodule 𝔽₂ (Fin n → 𝔽₂)) → (Submodule 𝔽₂ (Fin m → 𝔽₂)) →
      Triple m n → ℝ) :
    (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, G V₁ W₁ t.1) =
      ∑ t : Triple m n, G (trV₁ t) (trW₁ t) t := by
  have h1 : ∀ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∀ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
      (∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, G V₁ W₁ t.1) =
        ∑ t : Triple m n, (if TripleOK V₁ W₁ t then G V₁ W₁ t else 0) := by
    intro V₁ W₁
    rw [sum_ite_eq_sum_subtype (TripleOK V₁ W₁)]
  rw [Finset.sum_congr rfl (fun V₁ _ => Finset.sum_congr rfl (fun W₁ _ => h1 V₁ W₁))]
  have h2 : ∀ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∀ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
      ∀ t : Triple m n,
      (if TripleOK V₁ W₁ t then G V₁ W₁ t else 0) =
        (if V₁ = trV₁ t ∧ W₁ = trW₁ t then G (trV₁ t) (trW₁ t) t else 0) := by
    intro V₁ W₁ t
    by_cases h : TripleOK V₁ W₁ t
    · obtain ⟨hV, hW⟩ := (TripleOK_iff V₁ W₁ t).mp h
      rw [if_pos h, if_pos ⟨hV, hW⟩]
      rw [hV, hW]
    · rw [if_neg h]
      rw [if_neg (fun hc => h ((TripleOK_iff V₁ W₁ t).mpr hc))]
  rw [Finset.sum_congr rfl (fun V₁ _ => Finset.sum_congr rfl (fun W₁ _ =>
    Finset.sum_congr rfl (fun t _ => h2 V₁ W₁ t)))]
  -- swap the sums: first `W₁` with `t`, then `V₁` with `t`
  conv_lhs =>
    enter [2, V₁]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Submodule 𝔽₂ (Fin m → 𝔽₂))))
      (t := (Finset.univ : Finset (Triple m n)))
      (f := fun (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (t : Triple m n) =>
        (if V₁ = trV₁ t ∧ W₁ = trW₁ t then G (trV₁ t) (trW₁ t) t else 0))]
  conv_lhs =>
    rw [Finset.sum_comm (s := (Finset.univ : Finset (Submodule 𝔽₂ (Fin n → 𝔽₂))))
      (t := (Finset.univ : Finset (Triple m n)))
      (f := fun (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (t : Triple m n) =>
        ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if V₁ = trV₁ t ∧ W₁ = trW₁ t then G (trV₁ t) (trW₁ t) t else 0))]
  -- evaluate the inner sums
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [Finset.sum_eq_single (trV₁ t)]
  · rw [Finset.sum_eq_single (trW₁ t)]
    · rw [if_pos ⟨rfl, rfl⟩]
    · intro W₁ _ hne
      rw [if_neg (fun hc => hne hc.2)]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · intro V₁ _ hne
    refine Finset.sum_eq_zero (fun W₁ _ => ?_)
    rw [if_neg (fun hc => hne hc.1)]
  · intro hnot
    exact absurd (Finset.mem_univ _) hnot

/-! ## `lem:after restricting` -/

/-- Exponent bookkeeping for `lem:after restricting`. -/
private lemma exp_bound (o ot d : ℕ) (h1 : o ≤ 2 * ot) (h2 : ot ≤ d) :
    7 * d * o + 3 * (o * o) ≤ 26 * d * ot := by
  have ho : o ≤ 2 * d := le_trans h1 (by omega)
  nlinarith [h1, ho, Nat.zero_le o]

/-- **`lem:after restricting`** (arXiv:2209.04243 §8): combining `lem:bounds on composition`
with `lem:hyp inductive step` and reindexing the quintuples by the triples gives

  `‖f‖₄⁴/162 ≤ q^{6d²}‖f‖₂⁴ + Σ_{(V₂,W₂,X), |·|>0} q^{24d|(V₂,W₂,X)|} E_T‖D_X D_{V₂,W₂,T}[f]‖₄⁴`. -/
theorem after_restricting {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    l4q f ≤ 162 * 2 ^ (6 * d ^ 2) * (l2sq f) ^ 2 +
      2 * (((2 : ℝ) ^ (m * n))⁻¹ * ∑ t : Triple m n,
        (if totOrder t = 0 then 0
         else 2 ^ (26 * d * totOrder t) *
           ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
             l4q (DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f))) := by
  -- Step 1: `hyp inductive step` with the sum over pairs
  refine le_trans (hyp_inductive_step_reindex (d := d) (f := f) hf) ?_
  -- Step 2: `bounds on composition` for each pair
  have hstep2 : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
          else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
          l4q (Lup V₁ (Ldown W₁ f))) ≤
      ((2 : ℝ) ^ (m * n))⁻¹ *
        (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
          else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
          ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
              (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
            ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
              l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun V₁ _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun W₁ _ => ?_)
    have hWnn : (0 : ℝ) ≤ (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then
        (0 : ℝ) else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) := by
      by_cases h : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0
      · rw [if_pos h]
      · rw [if_neg h]
        exact le_of_lt (pow_pos (by norm_num : (0:ℝ) < 2) _)
    refine (mul_le_mul_of_nonneg_left (bounds_on_composition V₁ W₁ f) hWnn).trans
      (le_of_eq ?_)
    ring
  refine le_trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hstep2
    (by norm_num : (0 : ℝ) ≤ 2))) ?_
  -- Step 3: reindex by the triples
  have hstep3 : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
          else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
          ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
              (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
            ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
              l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f))) =
      ∑ t : Triple m n,
        ((if Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t)) = 0 then 0
          else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ (trV₁ t) +
            (m - Module.finrank 𝔽₂ (trW₁ t))))) *
          ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ (trV₁ t) +
              (m - Module.finrank 𝔽₂ (trW₁ t))) *
              (Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t))))) *
            ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
              l4q (DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f))) := by
    have h3a : (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
            else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
            ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
                (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
              ∑ t : {t : Triple m n // TripleOK V₁ W₁ t}, ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
                l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f))) =
        ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
          ∑ t : {t : Triple m n // TripleOK V₁ W₁ t},
            (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) = 0 then 0
              else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
            ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
                (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
              ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
                l4q (DopX V₁ W₁ t.1.1 t.1.2.1 t.1.2.2 T f)) := by
      refine Finset.sum_congr rfl (fun V₁ _ => Finset.sum_congr rfl (fun W₁ _ => ?_))
      rw [← mul_assoc, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      rw [mul_assoc]
    refine h3a.trans ?_
    exact reindex_triples (fun V₁ W₁ t => (if Module.finrank 𝔽₂ V₁ +
          (m - Module.finrank 𝔽₂ W₁) = 0 then 0
        else (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
        ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)) *
            (Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁)))) *
          ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
            l4q (DopX V₁ W₁ t.1 t.2.1 t.2.2 T f)))
  rw [hstep3]
  -- Step 4: bound the weights
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2))
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun t _ => ?_)
  by_cases ht0 : totOrder t = 0
  · rw [if_pos ht0]
    -- the weight is `0` because the order of the section is `0`
    have hrank : Module.finrank 𝔽₂ (LinearMap.range t.2.2) ≤ totOrder t := by
      rw [totOrder]; omega
    have hord : Module.finrank 𝔽₂ (trV₁ t) +
        (m - Module.finrank 𝔽₂ (trW₁ t)) = 0 := by
      have h := order_section t
      omega
    rw [if_pos hord, zero_mul]
  · rw [if_neg ht0]
    by_cases hd : totOrder t ≤ d
    · -- nonzero order and `totOrder t ≤ d`: bound the weight
      have hord : Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t)) ≠ 0 := by
        intro h
        apply ht0
        have h2 := order_section t
        have hrank : Module.finrank 𝔽₂ (LinearMap.range t.2.2) ≤ totOrder t := by
          rw [totOrder]; omega
        omega
      rw [if_neg hord]
      have hle := order_section_le t
      have hexp := exp_bound (Module.finrank 𝔽₂ (trV₁ t) +
        (m - Module.finrank 𝔽₂ (trW₁ t))) (totOrder t) d hle hd
      have hcomb : (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ (trV₁ t) +
            (m - Module.finrank 𝔽₂ (trW₁ t)))) *
          ((2 : ℝ) ^ (3 * ((Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t))) *
              (Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t))))) *
            ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
              l4q (DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) =
        (2 : ℝ) ^ (7 * d * (Module.finrank 𝔽₂ (trV₁ t) +
            (m - Module.finrank 𝔽₂ (trW₁ t))) +
          3 * ((Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t))) *
              (Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t))))) *
          ∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
            l4q (DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f) := by
        rw [← mul_assoc, ← pow_add]
      rw [hcomb]
      refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun T _ => l4q_nonneg _))
      exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
    · -- `d < totOrder t`: the sum vanishes
      have hzero : (∑ T : Matrix (Fin m) (Fin n) 𝔽₂,
          l4q (DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 T f)) = 0 := by
        refine Finset.sum_eq_zero (fun T _ => ?_)
        rw [DopX_eq_zero_of_degLe hf (trV₁ t) (trW₁ t) T (by
          rw [totOrder] at hd
          omega)]
        simp [l4q]
      rw [hzero, mul_zero]
      by_cases hord : Module.finrank 𝔽₂ (trV₁ t) + (m - Module.finrank 𝔽₂ (trW₁ t)) = 0
      · rw [if_pos hord]; simp
      · rw [if_neg hord]; simp

end

end Submission.Grassmann

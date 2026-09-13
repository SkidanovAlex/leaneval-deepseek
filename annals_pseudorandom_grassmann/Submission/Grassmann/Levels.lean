import Mathlib
import Submission.Grassmann.Injective

/-!
# The level decomposition of functions on the Grassmann graph

Once `Ψ_i` is known to be injective (`2ℓ ≤ k`, see `Injective.lean`) the filtration
`V_0 ≤ V_1 ≤ ⋯ ≤ V_ℓ = ⊤` is strictly increasing with `dim V_i = [k choose i]_2`, and
`(A - θ_i) V_i ≤ V_{i-1}`.

This file shows that the quotients `V_i / V_{i-1}` can be realised as the *orthogonal*
subspaces `L_i = V_i ⊓ V_{i-1}^⊥` (for the standard inner product on `ℚ`-valued functions)
and that `A = θ_i` on `L_i`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

attribute [local instance] Classical.propDecidable

variable {k ℓ : ℕ}

/-! ## 1. The standard inner product on functions -/

/-- The standard (positive definite) inner product on `ℚ`-valued functions on a finite type. -/
def stdInner (k ℓ : ℕ) : LinearMap.BilinForm ℚ (GrVertex k ℓ → ℚ) :=
  Matrix.toBilin' (1 : Matrix (GrVertex k ℓ) (GrVertex k ℓ) ℚ)

lemma stdInner_apply (f g : GrVertex k ℓ → ℚ) :
    stdInner k ℓ f g = ∑ L, f L * g L := by
  rw [stdInner, Matrix.toBilin'_apply]
  simp [Matrix.one_apply]

lemma stdInner_comm (f g : GrVertex k ℓ → ℚ) :
    stdInner k ℓ f g = stdInner k ℓ g f := by
  rw [stdInner_apply, stdInner_apply]
  exact Finset.sum_congr rfl (fun L _ => mul_comm _ _)

lemma stdInner_isRefl (k ℓ : ℕ) : (stdInner k ℓ).IsRefl := by
  intro f g h
  rw [stdInner_comm]; exact h

lemma stdInner_nondegenerate (k ℓ : ℕ) : (stdInner k ℓ).Nondegenerate := by
  rw [stdInner]
  exact Matrix.Nondegenerate.toBilin' (Matrix.nondegenerate_of_det_ne_zero (by simp))

/-- The standard inner product is positive definite. -/
lemma stdInner_pos {f : GrVertex k ℓ → ℚ} (hf : f ≠ 0) : 0 < stdInner k ℓ f f := by
  rw [stdInner_apply]
  obtain ⟨L, hL⟩ : ∃ L, f L ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext fun L => h L)
  exact Finset.sum_pos' (fun M _ => mul_self_nonneg _)
    ⟨L, Finset.mem_univ L, mul_self_pos.mpr hL⟩

/-! ## 2. Orthogonal complements in the function space -/

/-- `W ⊓ W^⊥ = ⊥` by positive definiteness. -/
lemma inf_ortho_bot (W : Submodule ℚ (GrVertex k ℓ → ℚ)) :
    W ⊓ (stdInner k ℓ).orthogonal W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  rw [Submodule.mem_inf] at hf
  by_contra hne
  have h1 := (LinearMap.BilinForm.mem_orthogonal_iff.mp hf.2) f hf.1
  have h2 := stdInner_pos (k := k) (ℓ := ℓ) hne
  rw [h1] at h2
  exact lt_irrefl _ h2

/-- `W ⊔ W^⊥ = ⊤`. -/
lemma sup_ortho_top (W : Submodule ℚ (GrVertex k ℓ → ℚ)) :
    W ⊔ (stdInner k ℓ).orthogonal W = ⊤ := by
  refine Submodule.eq_top_of_finrank_eq ?_
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq W ((stdInner k ℓ).orthogonal W)
  rw [inf_ortho_bot (k := k) (ℓ := ℓ) W, finrank_bot, add_zero,
    LinearMap.BilinForm.finrank_orthogonal (stdInner_nondegenerate k ℓ)] at h1
  rw [h1]
  have hle : Module.finrank ℚ ↥W ≤ Module.finrank ℚ (GrVertex k ℓ → ℚ) := Submodule.finrank_le W
  omega

/-- The orthogonal projection: every vector splits as `w + u` with `w ∈ W` and `u ∈ W^⊥`. -/
lemma exists_add_mem_ortho (W : Submodule ℚ (GrVertex k ℓ → ℚ)) (v : GrVertex k ℓ → ℚ) :
    ∃ w ∈ W, ∃ u ∈ (stdInner k ℓ).orthogonal W, w + u = v := by
  have hv : v ∈ W ⊔ (stdInner k ℓ).orthogonal W := by
    rw [sup_ortho_top (k := k) (ℓ := ℓ) W]; exact Submodule.mem_top
  rwa [Submodule.mem_sup] at hv

/-! ## 3. The level spaces -/

/-- The level-`i` subspace `L_i = V_i ⊓ V_{i-1}^⊥`. -/
def Lvl (k ℓ : ℕ) (i : ℕ) : Submodule ℚ (GrVertex k ℓ → ℚ) :=
  Vup (k := k) (ℓ := ℓ) i ⊓ (stdInner k ℓ).orthogonal (Vup (k := k) (ℓ := ℓ) (i - 1))

/-- `A` preserves every level space `V_i` (including `V_0`, the constants). -/
lemma adjOpLM_mem_Vup' (hℓ : 1 ≤ ℓ) (i : ℕ) (hiℓ : i ≤ ℓ)
    {x : GrVertex k ℓ → ℚ} (hx : x ∈ Vup (k := k) (ℓ := ℓ) i) :
    adjOpLM (k := k) (ℓ := ℓ) x ∈ Vup (k := k) (ℓ := ℓ) i := by
  rcases Nat.eq_zero_or_pos i with h | h
  · subst h
    have hz := adjOpLM_sub_theta_zero_mem (k := k) (ℓ := ℓ) hℓ hx
    rw [sub_eq_zero] at hz
    rw [hz]
    exact Submodule.smul_mem _ _ hx
  · exact adjOpLM_mem_Vup (k := k) (ℓ := ℓ) hℓ i h hiℓ hx

/-- `V_i = V_{i-1} ⊕ L_i`. -/
lemma Vup_eq_sup_Lvl (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ) :
    Vup (k := k) (ℓ := ℓ) i
      = Vup (k := k) (ℓ := ℓ) (i - 1) ⊔ Lvl k ℓ i := by
  classical
  refine le_antisymm ?_ (sup_le (Vup_pred_le (k := k) (ℓ := ℓ) hℓ i hi hiℓ) inf_le_left)
  intro v hv
  obtain ⟨w, hw, u, hu, hwu⟩ := exists_add_mem_ortho (k := k) (ℓ := ℓ)
    (Vup (k := k) (ℓ := ℓ) (i - 1)) v
  rw [Submodule.mem_sup]
  refine ⟨w, hw, u, ?_, hwu⟩
  rw [Lvl, Submodule.mem_inf]
  refine ⟨?_, hu⟩
  have huw : u = v - w := by rw [← hwu]; abel
  rw [huw]
  exact Submodule.sub_mem _ hv (Vup_pred_le (k := k) (ℓ := ℓ) hℓ i hi hiℓ hw)

/-- The level spaces have dimension `[k choose i]_2 - [k choose i-1]_2`. -/
lemma finrank_Lvl (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ) (hk : 2 * ℓ ≤ k) :
    Module.finrank ℚ ↥(Lvl k ℓ i) = grCount k i - grCount k (i - 1) := by
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq
    (Vup (k := k) (ℓ := ℓ) (i - 1)) (Lvl k ℓ i)
  have hdisj : Vup (k := k) (ℓ := ℓ) (i - 1) ⊓ Lvl k ℓ i = ⊥ := by
    rw [Lvl, ← inf_assoc, inf_eq_left.mpr (Vup_pred_le (k := k) (ℓ := ℓ) hℓ i hi hiℓ)]
    exact inf_ortho_bot (k := k) (ℓ := ℓ) (Vup (k := k) (ℓ := ℓ) (i - 1))
  rw [hdisj, finrank_bot, add_zero, ← Vup_eq_sup_Lvl (k := k) (ℓ := ℓ) hℓ i hi hiℓ] at hfr
  have hL : Module.finrank ℚ ↥(Lvl k ℓ i)
      = Module.finrank ℚ ↥(Vup (k := k) (ℓ := ℓ) i)
        - Module.finrank ℚ ↥(Vup (k := k) (ℓ := ℓ) (i - 1)) := by omega
  rw [hL, finrank_Vup_le i ℓ hℓ hiℓ hk, finrank_Vup_le (i - 1) ℓ hℓ (by omega) hk]

/-- **`A = θ_i` on the level space `L_i`.** -/
theorem adjOp_eq_theta_of_mem_Lvl (hℓ : 1 ≤ ℓ) (i : ℕ) (hi : 1 ≤ i) (hiℓ : i ≤ ℓ)
    {f : GrVertex k ℓ → ℚ} (hf : f ∈ Lvl k ℓ i) :
    adjOpLM (k := k) (ℓ := ℓ) f = thetaQ k ℓ i • f := by
  classical
  rw [Lvl, Submodule.mem_inf] at hf
  obtain ⟨hf1, hf2⟩ := hf
  have hf2' : ∀ u ∈ Vup (k := k) (ℓ := ℓ) (i - 1), stdInner k ℓ f u = 0 := by
    intro u hu
    rw [stdInner_comm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hf2) u hu
  have hw : adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f
      ∈ Vup (k := k) (ℓ := ℓ) (i - 1) :=
    adjOpLM_sub_mem_Vup_pred (k := k) (ℓ := ℓ) hℓ i hi hiℓ hf1
  have hw2 : adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f
      ∈ (stdInner k ℓ).orthogonal (Vup (k := k) (ℓ := ℓ) (i - 1)) := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hAu : adjOpLM (k := k) (ℓ := ℓ) u ∈ Vup (k := k) (ℓ := ℓ) (i - 1) :=
      adjOpLM_mem_Vup' (k := k) (ℓ := ℓ) hℓ (i - 1) (by omega) hu
    have h1 : ∑ L, adjOpLM (k := k) (ℓ := ℓ) f L * u L
        = ∑ L, f L * adjOpLM (k := k) (ℓ := ℓ) u L := by
      simpa only [adjOpLM_apply] using (adjOp_comm (k := k) (ℓ := ℓ) f u).symm
    have h2 : (∑ L, f L * adjOpLM (k := k) (ℓ := ℓ) u L) = 0 := by
      have := hf2' _ hAu
      rwa [stdInner_apply] at this
    have h3 : (∑ L, f L * u L) = 0 := by
      have := hf2' u hu
      rwa [stdInner_apply] at this
    rw [stdInner_apply]
    have hswap : ∑ L, u L * (adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f) L
        = ∑ L, (adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f) L * u L :=
      Finset.sum_congr rfl (fun L _ => mul_comm _ _)
    have hexp : ∑ L, (adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f) L * u L
        = (∑ L, adjOpLM (k := k) (ℓ := ℓ) f L * u L)
          - thetaQ k ℓ i * (∑ L, f L * u L) := by
      have hpt : ∀ L, (adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f) L * u L
          = adjOpLM (k := k) (ℓ := ℓ) f L * u L - thetaQ k ℓ i * (f L * u L) := by
        intro L
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [Finset.sum_congr rfl (fun L _ => hpt L), Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hswap, hexp, h1, h2, h3]; ring
  have hbot : adjOpLM (k := k) (ℓ := ℓ) f - thetaQ k ℓ i • f
      ∈ (⊥ : Submodule ℚ (GrVertex k ℓ → ℚ)) := by
    rw [← inf_ortho_bot (k := k) (ℓ := ℓ) (Vup (k := k) (ℓ := ℓ) (i - 1))]
    exact Submodule.mem_inf.mpr ⟨hw, hw2⟩
  exact sub_eq_zero.mp (by simpa using hbot)

/-- The level spaces are monotone in `i`. -/
lemma Vup_mono (hℓ : 1 ≤ ℓ) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ ℓ) :
    Vup (k := k) (ℓ := ℓ) i ≤ Vup (k := k) (ℓ := ℓ) j := by
  have key : ∀ m, i + m ≤ ℓ → Vup (k := k) (ℓ := ℓ) i ≤ Vup (k := k) (ℓ := ℓ) (i + m) := by
    intro m
    induction m with
    | zero => intro _; exact le_rfl
    | succ m ih =>
        intro hm
        exact le_trans (ih (by omega))
          (Vup_pred_le (k := k) (ℓ := ℓ) hℓ (i + m + 1) (by omega) (by omega))
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  exact key d hj

/-- `W ≤ (W^⊥)^⊥`. -/
lemma le_double_ortho (W : Submodule ℚ (GrVertex k ℓ → ℚ)) :
    W ≤ (stdInner k ℓ).orthogonal ((stdInner k ℓ).orthogonal W) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [stdInner_comm]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hy) x hx

/-- Orthogonality is symmetric. -/
lemma le_ortho_comm {U W : Submodule ℚ (GrVertex k ℓ → ℚ)} :
    U ≤ (stdInner k ℓ).orthogonal W ↔ W ≤ (stdInner k ℓ).orthogonal U := by
  constructor
  · intro h x hx
    have hx' : ∀ y ∈ U, (stdInner k ℓ) y x = 0 := by
      intro y hy
      have hy' := h hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy'
      rw [stdInner_comm]
      exact hy' x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hx' y hy
  · intro h x hx
    have hx' : ∀ y ∈ W, (stdInner k ℓ) y x = 0 := by
      intro y hy
      have hy' := h hy
      rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy'
      rw [stdInner_comm]
      exact hy' x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro y hy
    exact hx' y hy

/-- The level spaces (`i ≥ 1`) are pairwise orthogonal. -/
lemma Lvl_orthogonal (hℓ : 1 ≤ ℓ) {i j : ℕ} (hi : 1 ≤ i) (hj : j ≤ ℓ) (hij : i < j) :
    Lvl k ℓ i ≤ (stdInner k ℓ).orthogonal (Lvl k ℓ j) := by
  refine le_trans inf_le_left (le_trans (Vup_mono (k := k) (ℓ := ℓ)
    (i := i) (j := j - 1) hℓ (by omega) (by omega)) ?_)
  refine le_trans (le_double_ortho (k := k) (ℓ := ℓ) (Vup (k := k) (ℓ := ℓ) (j - 1))) ?_
  exact LinearMap.BilinForm.orthogonal_le
    (inf_le_right : Lvl k ℓ j
      ≤ (stdInner k ℓ).orthogonal (Vup (k := k) (ℓ := ℓ) (j - 1)))

/-- The constants are orthogonal to each level space `L_j`, `j ≥ 1`. -/
lemma Vup0_le_ortho_Lvl (hℓ : 1 ≤ ℓ) {j : ℕ} (hj : j ≤ ℓ) (hjpos : 1 ≤ j) :
    Vup (k := k) (ℓ := ℓ) 0 ≤ (stdInner k ℓ).orthogonal (Lvl k ℓ j) := by
  refine le_trans (Vup_mono (k := k) (ℓ := ℓ) (i := 0) (j := j - 1) hℓ (by omega) (by omega)) ?_
  refine le_trans (le_double_ortho (k := k) (ℓ := ℓ) (Vup (k := k) (ℓ := ℓ) (j - 1))) ?_
  exact LinearMap.BilinForm.orthogonal_le
    (inf_le_right : Lvl k ℓ j
      ≤ (stdInner k ℓ).orthogonal (Vup (k := k) (ℓ := ℓ) (j - 1)))

/-! ## 4. The level decomposition and the eigenvalue expansion -/

/-- The level-`i` space, with level `0` being the one-dimensional space of constants. -/
def LvlAll (k ℓ : ℕ) (i : ℕ) : Submodule ℚ (GrVertex k ℓ → ℚ) :=
  if i = 0 then Vup (k := k) (ℓ := ℓ) 0 else Lvl k ℓ i

lemma LvlAll_zero (k ℓ : ℕ) : LvlAll k ℓ 0 = Vup (k := k) (ℓ := ℓ) 0 := if_pos rfl

lemma LvlAll_succ {i : ℕ} (hi : i ≠ 0) : LvlAll k ℓ i = Lvl k ℓ i := if_neg hi

/-- The spaces `LvlAll` are pairwise orthogonal. -/
lemma LvlAll_orthogonal (hℓ : 1 ≤ ℓ) {i j : ℕ} (hi : i ≤ ℓ) (hj : j ≤ ℓ) (hij : i ≠ j) :
    LvlAll k ℓ i ≤ (stdInner k ℓ).orthogonal (LvlAll k ℓ j) := by
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · exact absurd hj0.symm hij
    · rw [LvlAll_zero, LvlAll_succ (by omega)]
      exact Vup0_le_ortho_Lvl (k := k) (ℓ := ℓ) hℓ hj hjpos
  · rw [LvlAll_succ (by omega)]
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [LvlAll_zero]
      exact (le_ortho_comm (k := k) (ℓ := ℓ) (U := Vup (k := k) (ℓ := ℓ) 0)
        (W := Lvl k ℓ i)).mp (Vup0_le_ortho_Lvl (k := k) (ℓ := ℓ) hℓ hi (by omega))
    · rw [LvlAll_succ (by omega)]
      rcases lt_or_gt_of_ne hij with h | h
      · exact Lvl_orthogonal (k := k) (ℓ := ℓ) hℓ (by omega) hj h
      · exact (le_ortho_comm (k := k) (ℓ := ℓ) (U := Lvl k ℓ j) (W := Lvl k ℓ i)).mp
          (Lvl_orthogonal (k := k) (ℓ := ℓ) hℓ (by omega) hi h)

/-- `A = θ_i` on the level space `LvlAll i`. -/
lemma adjOp_eq_theta_of_mem_LvlAll (hℓ : 1 ≤ ℓ) {i : ℕ} (hi : i ≤ ℓ)
    {f : GrVertex k ℓ → ℚ} (hf : f ∈ LvlAll k ℓ i) :
    adjOpLM (k := k) (ℓ := ℓ) f = thetaQ k ℓ i • f := by
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · subst hi0
    rw [LvlAll_zero] at hf
    exact sub_eq_zero.mp (adjOpLM_sub_theta_zero_mem (k := k) (ℓ := ℓ) hℓ hf)
  · rw [LvlAll_succ (by omega)] at hf
    exact adjOp_eq_theta_of_mem_Lvl (k := k) (ℓ := ℓ) hℓ i hipos (by omega) hf

/-- **`Fun = ⊕_{i ≤ ℓ} LvlAll i`**: given `f`, there are components `g i ∈ LvlAll i`
summing to `f`, and the inner products expand accordingly. -/
theorem inner_adjOp_eq_sum_Lvl (hℓ : 1 ≤ ℓ) (hk : 2 * ℓ ≤ k) (f : GrVertex k ℓ → ℚ) :
    ∃ g : ℕ → (GrVertex k ℓ → ℚ),
      (∀ i, i ≤ ℓ → g i ∈ LvlAll k ℓ i) ∧
      (∀ i, i ≤ ℓ → f - g i ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ i)) ∧
      (∑ i ∈ Finset.range (ℓ + 1), g i) = f ∧
      stdInner k ℓ f f = ∑ i ∈ Finset.range (ℓ + 1), stdInner k ℓ (g i) (g i) ∧
      stdInner k ℓ (adjOpLM (k := k) (ℓ := ℓ) f) f
        = ∑ i ∈ Finset.range (ℓ + 1), thetaQ k ℓ i * stdInner k ℓ (g i) (g i) := by
  classical
  have hchoose : ∀ i : ℕ, ∃ w : GrVertex k ℓ → ℚ,
      w ∈ LvlAll k ℓ i ∧ f - w ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ i) := by
    intro i
    obtain ⟨w, hw, u, hu, hwu⟩ := exists_add_mem_ortho (k := k) (ℓ := ℓ) (LvlAll k ℓ i) f
    refine ⟨w, hw, ?_⟩
    have : f - w = u := by rw [← hwu]; abel
    rw [this]; exact hu
  set g : ℕ → (GrVertex k ℓ → ℚ) := fun i => Classical.choose (hchoose i) with hg
  have hg_mem : ∀ i, g i ∈ LvlAll k ℓ i := fun i => (Classical.choose_spec (hchoose i)).1
  have hg_orth : ∀ i, f - g i ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ i) :=
    fun i => (Classical.choose_spec (hchoose i)).2
  -- `f` is the sum of the `g i`
  have hperp : ∀ i, i ≤ ℓ → f - ∑ j ∈ Finset.range (ℓ + 1), g j
      ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ i) := by
    intro i hi
    have hmem : (∑ j ∈ (Finset.range (ℓ + 1)).erase i, g j)
        ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ i) := by
      refine Submodule.sum_mem _ (fun j hj => ?_)
      rw [Finset.mem_erase] at hj
      obtain ⟨hji, hjrange⟩ := hj
      rw [Finset.mem_range] at hjrange
      exact LvlAll_orthogonal (k := k) (ℓ := ℓ) (i := j) (j := i) hℓ
        (by omega : j ≤ ℓ) hi hji (hg_mem j)
    have hsplit : (∑ j ∈ Finset.range (ℓ + 1), g j) - g i
        = ∑ j ∈ (Finset.range (ℓ + 1)).erase i, g j := by
      have h := Finset.sum_erase_add (Finset.range (ℓ + 1)) g
        (Finset.mem_range.mpr (by omega : i < ℓ + 1))
      rw [← h]
      abel
    rw [show f - ∑ j ∈ Finset.range (ℓ + 1), g j
        = (f - g i) - ((∑ j ∈ Finset.range (ℓ + 1), g j) - g i) by abel]
    rw [hsplit]
    exact Submodule.sub_mem _ (hg_orth i) hmem
  -- the levels span
  have hspan : ∀ m ≤ ℓ, (Finset.range (m + 1)).sup (LvlAll k ℓ) = Vup (k := k) (ℓ := ℓ) m := by
    intro m hm
    induction m with
    | zero => simp [Finset.range_one, LvlAll_zero]
    | succ m ih =>
        rw [Finset.range_add_one, Finset.sup_insert, ih (by omega),
          LvlAll_succ (by omega), sup_comm]
        show Vup (k := k) (ℓ := ℓ) (m + 1 - 1) ⊔ Lvl k ℓ (m + 1)
          = Vup (k := k) (ℓ := ℓ) (m + 1)
        rw [← Vup_eq_sup_Lvl (k := k) (ℓ := ℓ) hℓ (m + 1) (by omega) (by omega)]
  -- an element orthogonal to all levels is zero
  have hsup_ortho : ∀ (s : Finset ℕ) (x : GrVertex k ℓ → ℚ),
      (∀ i ∈ s, x ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ i)) →
      x ∈ (stdInner k ℓ).orthogonal (s.sup (LvlAll k ℓ)) := by
    intro s
    induction s using Finset.induction with
    | empty => intro x _; simp
    | insert a s ha ih =>
        intro x h
        rw [Finset.sup_insert, LinearMap.BilinForm.mem_orthogonal_iff]
        intro y hy
        rw [Submodule.mem_sup] at hy
        obtain ⟨u, hu, v, hv, huv⟩ := hy
        have ha' : x ∈ (stdInner k ℓ).orthogonal (LvlAll k ℓ a) :=
          h a (Finset.mem_insert_self a s)
        rw [LinearMap.BilinForm.mem_orthogonal_iff] at ha'
        have hs' : x ∈ (stdInner k ℓ).orthogonal (s.sup (LvlAll k ℓ)) :=
          ih x (fun i hi => h i (Finset.mem_insert.mpr (Or.inr hi)))
        rw [LinearMap.BilinForm.mem_orthogonal_iff] at hs'
        have h1 : (stdInner k ℓ) (u + v) x
            = (stdInner k ℓ) u x + (stdInner k ℓ) v x := by
          rw [map_add, LinearMap.add_apply]
        rw [← huv, h1, ha' u hu, hs' v hv, add_zero]
  have hsum_eq : (∑ j ∈ Finset.range (ℓ + 1), g j) = f := by
    have hx := hsup_ortho (Finset.range (ℓ + 1)) (f - ∑ j ∈ Finset.range (ℓ + 1), g j)
      (fun i hi => hperp i (by rw [Finset.mem_range] at hi; omega))
    rw [hspan ℓ le_rfl, Vup_self,
      LinearMap.BilinForm.orthogonal_top_eq_bot (stdInner_nondegenerate k ℓ)] at hx
    have hx0 : f - ∑ j ∈ Finset.range (ℓ + 1), g j = 0 := by simpa using hx
    exact (sub_eq_zero.mp hx0).symm
  -- the components are pairwise orthogonal
  have horth_ij : ∀ i j, i ≤ ℓ → j ≤ ℓ → i ≠ j →
      stdInner k ℓ (g i) (g j) = 0 := by
    intro i j hi hj hij
    have h := LvlAll_orthogonal (k := k) (ℓ := ℓ) hℓ hi hj hij (hg_mem i)
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at h
    rw [stdInner_comm]
    exact h (g j) (hg_mem j)
  -- expansion in the second argument
  have hexpand : ∀ u : GrVertex k ℓ → ℚ,
      stdInner k ℓ u (∑ j ∈ Finset.range (ℓ + 1), g j)
        = ∑ j ∈ Finset.range (ℓ + 1), stdInner k ℓ u (g j) := by
    intro u
    rw [stdInner_apply]
    have step : ∀ L : GrVertex k ℓ,
        u L * (∑ j ∈ Finset.range (ℓ + 1), g j) L
          = ∑ j ∈ Finset.range (ℓ + 1), u L * g j L := by
      intro L
      rw [Finset.sum_apply, Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun L _ => step L), Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [stdInner_apply]
  -- expansion in the first argument
  have hexpand_left : ∀ (F : ℕ → GrVertex k ℓ → ℚ) (v : GrVertex k ℓ → ℚ),
      stdInner k ℓ (∑ j ∈ Finset.range (ℓ + 1), F j) v
        = ∑ j ∈ Finset.range (ℓ + 1), stdInner k ℓ (F j) v := by
    intro F v
    rw [map_sum, LinearMap.sum_apply]
  have hsingle : ∀ i ∈ Finset.range (ℓ + 1),
      (∑ j ∈ Finset.range (ℓ + 1), stdInner k ℓ (g i) (g j))
        = stdInner k ℓ (g i) (g i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    refine Finset.sum_eq_single i ?_ ?_
    · intro j hj hjne
      rw [Finset.mem_range] at hj
      exact horth_ij i j (by omega) (by omega) (Ne.symm hjne)
    · intro hnotin
      exact absurd (Finset.mem_range.mpr (by omega : i < ℓ + 1)) hnotin
  refine ⟨g, fun i _ => hg_mem i, fun i _ => hg_orth i, hsum_eq, ?_, ?_⟩
  · rw [← hsum_eq]
    have h1 : stdInner k ℓ (∑ i ∈ Finset.range (ℓ + 1), g i)
          (∑ j ∈ Finset.range (ℓ + 1), g j)
        = ∑ i ∈ Finset.range (ℓ + 1),
            ∑ j ∈ Finset.range (ℓ + 1), stdInner k ℓ (g i) (g j) := by
      rw [hexpand_left g]
      exact Finset.sum_congr rfl (fun i _ => hexpand (g i))
    rw [h1, Finset.sum_congr rfl hsingle]
  · rw [← hsum_eq]
    have h1 : adjOpLM (k := k) (ℓ := ℓ) (∑ j ∈ Finset.range (ℓ + 1), g j)
        = ∑ j ∈ Finset.range (ℓ + 1), adjOpLM (k := k) (ℓ := ℓ) (g j) := map_sum _ _ _
    rw [h1, hexpand_left (fun j => adjOpLM (k := k) (ℓ := ℓ) (g j))]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [adjOp_eq_theta_of_mem_LvlAll (k := k) (ℓ := ℓ) hℓ (by omega) (hg_mem i)]
    rw [show stdInner k ℓ (thetaQ k ℓ i • g i) (∑ j ∈ Finset.range (ℓ + 1), g j)
        = thetaQ k ℓ i * stdInner k ℓ (g i) (∑ j ∈ Finset.range (ℓ + 1), g j) from by
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul]]
    rw [hexpand (g i), hsingle i (Finset.mem_range.mpr hi)]

end

end F2
end Submission.Grassmann

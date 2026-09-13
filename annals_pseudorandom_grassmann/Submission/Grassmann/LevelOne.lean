import Mathlib
import Submission.Grassmann.LevelWeight

/-!
# The level-`1` space of `Gr k ℓ`

The level-`1` space of `Gr k ℓ` is `LvlAll k ℓ 1 = V_1 ⊓ V_0^⊥`, where the *up operator*
`Ψ_1` is `(Ψ_1 g)(L) = ∑_{W ≤ L, dim W = 1} g W`.

This file shows that the level-`1` space is, up to an explicit scale factor, the space of
zero-mean functions on the Grassmannian of lines:

`⟨Ψ₁ g, Ψ₁ g'⟩ = A · (∑ g)(∑ g') + (B - A) · ⟨g, g'⟩`, with
`A = [k-2 choose ℓ-2]_2`, `B = [k-1 choose ℓ-1]_2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open PseudorandomGrassmann
open Module Finset Filter
open Classical

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann
namespace F2

noncomputable section

variable {k ℓ : ℕ}

attribute [local instance] Classical.propDecidable

/-! ## 1. Counting the `ℓ`-subspaces containing a fixed subspace -/

lemma card_filter_superspaces (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) (n : ℕ)
    (hU : Module.finrank 𝔽₂ U ≤ n) :
    ((Finset.univ.filter (fun L : GrVertex k n => U ≤ L.1)).card : ℚ)
      = (grCount (k - Module.finrank 𝔽₂ U) (n - Module.finrank 𝔽₂ U) : ℚ) := by
  rw [← Fintype.card_subtype (fun L : GrVertex k n => U ≤ L.1),
    ← Nat.card_eq_fintype_card]
  exact_mod_cast natCard_superspaces_GrVertex U n hU

/-- The number of `ℓ`-subspaces containing a fixed line. -/
lemma card_superspaces_line (W : GrVertex k 1) (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    ((Finset.univ.filter (fun L : GrVertex k ℓ => W.1 ≤ L.1)).card : ℚ)
      = (grCount (k - 1) (ℓ - 1) : ℚ) := by
  rw [card_filter_superspaces W.1 ℓ (by rw [W.2]; exact hℓ), W.2]

/-- The number of `ℓ`-subspaces containing a fixed plane. -/
lemma card_superspaces_plane (U : GrVertex k 2) (hℓ : 2 ≤ ℓ) (hk : ℓ ≤ k) :
    ((Finset.univ.filter (fun L : GrVertex k ℓ => U.1 ≤ L.1)).card : ℚ)
      = (grCount (k - 2) (ℓ - 2) : ℚ) := by
  rw [card_filter_superspaces U.1 ℓ (by rw [U.2]; exact hℓ), U.2]

/-! ## 2. Two distinct lines span a plane -/

lemma finrank_sup_lines (W W' : GrVertex k 1) (h : W ≠ W') :
    Module.finrank 𝔽₂ ↥(W.1 ⊔ W'.1) = 2 := by
  have hinf : Module.finrank 𝔽₂ ↥(W.1 ⊓ W'.1) = 0 := by
    by_contra hne
    have hbot : W.1 ⊓ W'.1 ≠ ⊥ := by
      intro hb
      rw [hb, finrank_bot] at hne
      exact hne rfl
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hxW : x ∈ W.1 := (Submodule.mem_inf.mp hx).1
    have hxW' : x ∈ W'.1 := (Submodule.mem_inf.mp hx).2
    have hspan : Module.finrank 𝔽₂ ↥(Submodule.span 𝔽₂ {x}) = 1 := by
      rw [finrank_span_singleton hx0]
    have hle1 : Submodule.span 𝔽₂ {x} ≤ W.1 := Submodule.span_le.mpr (by simpa using hxW)
    have hle2 : Submodule.span 𝔽₂ {x} ≤ W'.1 := Submodule.span_le.mpr (by simpa using hxW')
    have e1 : Submodule.span 𝔽₂ {x} = W.1 :=
      Submodule.eq_of_le_of_finrank_eq hle1 (by rw [hspan, W.2])
    have e2 : Submodule.span 𝔽₂ {x} = W'.1 :=
      Submodule.eq_of_le_of_finrank_eq hle2 (by rw [hspan, W'.2])
    exact h (Subtype.ext (e1 ▸ e2))
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq W.1 W'.1
  rw [hinf, W.2, W'.2] at hsup
  omega

/-! ## 3. The sum of `Ψ₁ g` over all vertices -/

lemma sum_upFun_one (g : GrVertex k 1 → ℚ) (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    ∑ L : GrVertex k ℓ, upFun 1 g L = (grCount (k - 1) (ℓ - 1) : ℚ) * ∑ W, g W := by
  have hterm : ∀ W : GrVertex k 1,
      (∑ L : GrVertex k ℓ, (if W.1 ≤ L.1 then g W else 0))
        = (grCount (k - 1) (ℓ - 1) : ℚ) * g W := by
    intro W
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul, card_superspaces_line W hℓ hk]
  calc ∑ L : GrVertex k ℓ, upFun 1 g L
      = ∑ L : GrVertex k ℓ, ∑ W : GrVertex k 1, (if W.1 ≤ L.1 then g W else 0) := rfl
    _ = ∑ W : GrVertex k 1, ∑ L : GrVertex k ℓ, (if W.1 ≤ L.1 then g W else 0) :=
        Finset.sum_comm
    _ = ∑ W : GrVertex k 1, (grCount (k - 1) (ℓ - 1) : ℚ) * g W :=
        Finset.sum_congr rfl (fun W _ => hterm W)
    _ = (grCount (k - 1) (ℓ - 1) : ℚ) * ∑ W, g W := by rw [Finset.mul_sum]

/-! ## 4. The two-point count -/

lemma sum_ite_le_le (W W' : GrVertex k 1) (c d : ℚ) (hℓ : 2 ≤ ℓ) (hk : ℓ ≤ k) :
    (∑ L : GrVertex k ℓ, (if W.1 ≤ L.1 then c else 0) * (if W'.1 ≤ L.1 then d else 0))
      = (if W = W' then (grCount (k - 1) (ℓ - 1) : ℚ) else (grCount (k - 2) (ℓ - 2) : ℚ))
          * (c * d) := by
  have hpt : ∀ L : GrVertex k ℓ,
      (if W.1 ≤ L.1 then c else 0) * (if W'.1 ≤ L.1 then d else 0)
        = if (W.1 ≤ L.1 ∧ W'.1 ≤ L.1) then c * d else 0 := by
    intro L
    by_cases h1 : W.1 ≤ L.1 <;> by_cases h2 : W'.1 ≤ L.1 <;> simp [h1, h2]
  rw [Finset.sum_congr rfl (fun L _ => hpt L)]
  by_cases hWW : W = W'
  · subst hWW
    have hset : (Finset.univ.filter (fun L : GrVertex k ℓ => W.1 ≤ L.1 ∧ W.1 ≤ L.1))
        = Finset.univ.filter (fun L : GrVertex k ℓ => W.1 ≤ L.1) := by
      ext L; simp
    rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul,
      card_superspaces_line W (by omega) hk, if_pos rfl]
  · have hfin : Module.finrank 𝔽₂ ↥(W.1 ⊔ W'.1) = 2 := finrank_sup_lines W W' hWW
    have hset : (Finset.univ.filter (fun L : GrVertex k ℓ => W.1 ≤ L.1 ∧ W'.1 ≤ L.1))
        = Finset.univ.filter (fun L : GrVertex k ℓ => (W.1 ⊔ W'.1) ≤ L.1) := by
      ext L
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun h => sup_le h.1 h.2,
        fun h => ⟨le_trans le_sup_left h, le_trans le_sup_right h⟩⟩
    have hb : ((Finset.univ.filter (fun L : GrVertex k ℓ => (W.1 ⊔ W'.1) ≤ L.1)).card : ℚ)
        = (grCount (k - 2) (ℓ - 2) : ℚ) := by
      rw [card_filter_superspaces (W.1 ⊔ W'.1) ℓ (by rw [hfin]; exact hℓ), hfin]
    rw [← Finset.sum_filter, hset, Finset.sum_const, nsmul_eq_mul, hb, if_neg hWW]

/-! ## 5. The two-point inner product formula -/

lemma sum_sum_const_mul (c : ℚ) (f : GrVertex k 1 → GrVertex k 1 → ℚ) :
    (∑ W : GrVertex k 1, ∑ W' : GrVertex k 1, c * f W W')
      = c * ∑ W : GrVertex k 1, ∑ W' : GrVertex k 1, f W W' := by
  simp only [Finset.mul_sum]

lemma sum_diag_one (g g' : GrVertex k 1 → ℚ) :
    (∑ W : GrVertex k 1, ∑ W' : GrVertex k 1,
        (if W = W' then (1 : ℚ) else 0) * (g W * g' W')) = stdInner k 1 g g' := by
  have hdiag : ∀ W : GrVertex k 1,
      (∑ W' : GrVertex k 1, (if W = W' then (1 : ℚ) else 0) * (g W * g' W'))
        = g W * g' W := by
    intro W
    rw [Finset.sum_eq_single W (fun W' _ hne => by
      by_cases h : W = W'
      · exact absurd h.symm hne
      · simp [h])
      (fun h => absurd (Finset.mem_univ W) h)]
    simp
  rw [Finset.sum_congr rfl (fun W _ => hdiag W), stdInner_apply]

lemma sum_sum_diag_mul (g g' : GrVertex k 1 → ℚ) :
    (∑ W : GrVertex k 1, ∑ W' : GrVertex k 1, g W * g' W')
      = (∑ W, g W) * (∑ W', g' W') := by
  rw [Finset.sum_mul_sum]

/-- **The two-point formula for `Ψ₁`.** -/
theorem stdInner_upFun_one (hℓ : 2 ≤ ℓ) (hk : ℓ ≤ k) (g g' : GrVertex k 1 → ℚ) :
    stdInner k ℓ (upFun 1 g) (upFun 1 g')
      = (grCount (k - 2) (ℓ - 2) : ℚ) * ((∑ W, g W) * (∑ W', g' W'))
        + ((grCount (k - 1) (ℓ - 1) : ℚ) - (grCount (k - 2) (ℓ - 2) : ℚ))
            * stdInner k 1 g g' := by
  set A : ℚ := (grCount (k - 2) (ℓ - 2) : ℚ) with hA
  set B : ℚ := (grCount (k - 1) (ℓ - 1) : ℚ) with hB
  have hstep : ∀ L : GrVertex k ℓ,
      upFun 1 g L * upFun 1 g' L
        = ∑ W : GrVertex k 1, ∑ W' : GrVertex k 1,
            (if W.1 ≤ L.1 then g W else 0) * (if W'.1 ≤ L.1 then g' W' else 0) := by
    intro L
    rw [upFun, upFun, Finset.sum_mul_sum]
  rw [stdInner_apply, Finset.sum_congr rfl (fun L _ => hstep L), Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun W (_ : W ∈ Finset.univ) => Finset.sum_comm)]
  rw [Finset.sum_congr rfl (fun W (_ : W ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun W' (_ : W' ∈ Finset.univ) =>
      sum_ite_le_le W W' (g W) (g' W') hℓ hk))]
  have hif : ∀ W W' : GrVertex k 1,
      (if W = W' then (grCount (k - 1) (ℓ - 1) : ℚ) else (grCount (k - 2) (ℓ - 2) : ℚ))
        = A + (B - A) * (if W = W' then (1 : ℚ) else 0) := by
    intro W W'
    by_cases h : W = W' <;> simp [h, hA, hB]
  rw [Finset.sum_congr rfl (fun W (_ : W ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun W' (_ : W' ∈ Finset.univ) => by rw [hif W W']))]
  have hpt : ∀ W W' : GrVertex k 1,
      (A + (B - A) * (if W = W' then (1 : ℚ) else 0)) * (g W * g' W')
        = A * (g W * g' W')
          + (B - A) * ((if W = W' then (1 : ℚ) else 0) * (g W * g' W')) := by
    intro W W'; ring
  rw [Finset.sum_congr rfl (fun W (_ : W ∈ Finset.univ) =>
    Finset.sum_congr rfl (fun W' (_ : W' ∈ Finset.univ) => hpt W W'))]
  rw [Finset.sum_congr rfl (fun W (_ : W ∈ Finset.univ) => Finset.sum_add_distrib)]
  rw [Finset.sum_add_distrib]
  have hA' : (∑ W : GrVertex k 1, ∑ W' : GrVertex k 1, A * (g W * g' W'))
      = A * ((∑ W, g W) * (∑ W', g' W')) := by
    rw [Finset.sum_congr rfl (fun W (_ : W ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun W' (_ : W' ∈ Finset.univ) =>
        show A * (g W * g' W') = (A * g W) * g' W' from by ring))]
    rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
    ring
  have hB' : (∑ W : GrVertex k 1, ∑ W' : GrVertex k 1,
        (B - A) * ((if W = W' then (1 : ℚ) else 0) * (g W * g' W')))
      = (B - A) * stdInner k 1 g g' := by
    rw [sum_sum_const_mul (B - A)
      (fun W W' => (if W = W' then (1 : ℚ) else 0) * (g W * g' W')),
      sum_diag_one g g']
  rw [hA', hB']

/-! ## 6. `Ψ₁` identifies the level-`1` space with the zero-mean functions on lines -/

/-- The linear functional `g ↦ ∑_W g W` on functions on the lines of `𝔽₂ᵏ`. -/
def sumLines (k : ℕ) : (GrVertex k 1 → ℚ) →ₗ[ℚ] ℚ where
  toFun g := ∑ W, g W
  map_add' g h := by simp [Finset.sum_add_distrib]
  map_smul' c g := by simp [Finset.mul_sum]

/-- The zero-mean functions on the Grassmannian of lines. -/
def zeroMean (k : ℕ) : Submodule ℚ (GrVertex k 1 → ℚ) := (sumLines k).ker

lemma mem_zeroMean {g : GrVertex k 1 → ℚ} : g ∈ zeroMean k ↔ ∑ W, g W = 0 := Iff.rfl

lemma grCount_pred_succ_ne_zero (hk : ℓ ≤ k) : grCount (k - 1) (ℓ - 1) ≠ 0 := by
  have h1 : 0 < grCount (k - 1) (ℓ - 1) := by
    rw [← card_GrVertex_eq_grCount]
    exact Fintype.card_pos_iff.mpr (nonempty_GrVertex_of_le (by omega))
  exact Nat.pos_iff_ne_zero.mp h1

lemma one_mem_Vup_zero : (fun _ : GrVertex k ℓ => (1 : ℚ)) ∈ Vup (k := k) (ℓ := ℓ) 0 :=
  ⟨fun _ => (1 : ℚ), by rw [upLM_apply, upFun_zero]⟩

/-- `Ψ₁ g` is orthogonal to the constants iff `g` has zero mean. -/
lemma upFun_one_ortho_one_iff (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) (g : GrVertex k 1 → ℚ) :
    stdInner k ℓ (upFun 1 g) (fun _ => (1 : ℚ)) = 0 ↔ ∑ W, g W = 0 := by
  rw [stdInner_apply]
  rw [Finset.sum_congr rfl (fun L (_ : L ∈ Finset.univ) => mul_one (upFun 1 g L)),
    sum_upFun_one g hℓ hk]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (Nat.cast_ne_zero.mpr (grCount_pred_succ_ne_zero (ℓ := ℓ) (k := k) (by omega)))
  · intro h; rw [h, mul_zero]

/-- **The level-`1` space, concretely**: `LvlAll k ℓ 1` is the image under `Ψ₁` of the
zero-mean functions on the lines. -/
theorem upFun_one_mem_LvlAll (hℓ : 2 ≤ ℓ) (hk : ℓ ≤ k) (g : GrVertex k 1 → ℚ) :
    upFun 1 g ∈ LvlAll k ℓ 1 ↔ g ∈ zeroMean k := by
  have hV1 : upFun 1 g ∈ Vup (k := k) (ℓ := ℓ) 1 := ⟨g, rfl⟩
  rw [LvlAll_succ (by norm_num : (1 : ℕ) ≠ 0), Lvl, Submodule.mem_inf, mem_zeroMean]
  constructor
  · intro h
    rw [← upFun_one_ortho_one_iff (k := k) (ℓ := ℓ) (by omega) hk g]
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at h
    rw [stdInner_comm]
    exact h.2 _ one_mem_Vup_zero
  · intro h
    refine ⟨hV1, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨c, rfl⟩ := Vup_zero_const hn
    rw [stdInner_apply, ← Finset.mul_sum, sum_upFun_one g (by omega) hk, h]
    ring

/-- **The key isometry.**  Restricted to zero-mean functions on the lines, `Ψ₁` is a
similarity with ratio `B - A`, `A = [k-2 choose ℓ-2]_2`, `B = [k-1 choose ℓ-1]_2`. -/
theorem stdInner_upFun_one_zeroMean (hℓ : 2 ≤ ℓ) (hk : ℓ ≤ k) {g g' : GrVertex k 1 → ℚ}
    (hg : g ∈ zeroMean k) (hg' : g' ∈ zeroMean k) :
    stdInner k ℓ (upFun 1 g) (upFun 1 g')
      = ((grCount (k - 1) (ℓ - 1) : ℚ) - (grCount (k - 2) (ℓ - 2) : ℚ))
          * stdInner k 1 g g' := by
  rw [stdInner_upFun_one hℓ hk g g']
  have h1 : (∑ W, g W) = 0 := hg
  have h2 : (∑ W', g' W') = 0 := hg'
  rw [h1, h2, mul_zero, mul_zero, zero_add]

/-- **Repackaging of the KMS second-moment step on the projective space.**  If `Φ(S) ≤ α`
and `2ℓ ≤ k`, the large level-`1` weight provided by `level_one_weight_ge` is realised by a
*zero-mean function on the lines*: `⟨Ψ₁ h, Ψ₁ h⟩ = (B - A)‖h‖²`. -/
theorem exists_zeroMean_level_one (hℓ : 2 ≤ ℓ) (hk : 2 * ℓ ≤ k) (S : Finset (GrVertex k ℓ))
    (hS : S.Nonempty) {α : ℚ} (hα : Φ (Gr k ℓ) S hS ≤ α) :
    ∃ h : GrVertex k 1 → ℚ, h ∈ zeroMean k ∧
      degQ k ℓ * (S.card : ℚ) * (1 - α - dens S)
          - thetaQ k ℓ 2 * ((S.card : ℚ) * (1 - dens S))
        ≤ (thetaQ k ℓ 1 - thetaQ k ℓ 2)
            * (((grCount (k - 1) (ℓ - 1) : ℚ) - (grCount (k - 2) (ℓ - 2) : ℚ))
                * stdInner k 1 h h) := by
  obtain ⟨g1, hg1, hle⟩ := level_one_weight_ge (k := k) (ℓ := ℓ) (by omega) hk S hS hα
  have hg1' : g1 ∈ Vup (k := k) (ℓ := ℓ) 1 := by
    have h := hg1
    rw [LvlAll_succ (by norm_num : (1 : ℕ) ≠ 0), Lvl, Submodule.mem_inf] at h
    exact h.1
  obtain ⟨h, rfl⟩ := hg1'
  have hh : h ∈ zeroMean k :=
    (upFun_one_mem_LvlAll (k := k) (ℓ := ℓ) hℓ (by omega : ℓ ≤ k) h).mp hg1
  refine ⟨h, hh, ?_⟩
  rw [upLM_apply] at hle
  rw [stdInner_upFun_one_zeroMean (k := k) (ℓ := ℓ) hℓ (by omega : ℓ ≤ k) hh hh] at hle
  exact hle

/-! ## 7. Lines are nonzero vectors: `Gr k 1 ≃ {v : 𝔽₂ᵏ // v ≠ 0}`

Over `𝔽₂` the only nonzero scalar is `1`, so a line is determined by its unique nonzero
vector.  This identifies the Grassmannian of lines (the projective space `PG(k-1,2)`) with
the set of nonzero vectors of `𝔽₂ᵏ`. -/

lemma finrank_one_exists_unique (L : GrVertex k 1) :
    ∃ v : Fin k → 𝔽₂, v ≠ 0 ∧ v ∈ L.1 ∧ ∀ w ∈ L.1, w ≠ 0 → w = v := by
  have hne : L.1 ≠ ⊥ := by
    intro h
    have h2 : Module.finrank 𝔽₂ ↥L.1 = 0 := by rw [h, finrank_bot]
    rw [L.2] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v, hv0, hv, ?_⟩
  intro w hw hw0
  have h1 : Submodule.span 𝔽₂ {w} ≤ L.1 := Submodule.span_le.mpr (by simpa using hw)
  have h2 : Module.finrank 𝔽₂ ↥(Submodule.span 𝔽₂ {w}) = 1 := finrank_span_singleton hw0
  have e1 : Submodule.span 𝔽₂ {w} = L.1 :=
    Submodule.eq_of_le_of_finrank_eq h1 (by rw [h2, L.2])
  have hv' : v ∈ Submodule.span 𝔽₂ {w} := by rw [e1]; exact hv
  rw [Submodule.mem_span_singleton] at hv'
  obtain ⟨c, hc⟩ := hv'
  have hc1 : c = 1 := zmod2_eq_one (fun hc0 => hv0 (by rw [hc0, zero_smul] at hc; exact hc.symm))
  rw [hc1, one_smul] at hc
  exact hc

/-- **Lines in `𝔽₂ᵏ` are nonzero vectors** (over `𝔽₂` the only nonzero scalar is `1`). -/
noncomputable def lineEquivNonzero (k : ℕ) : GrVertex k 1 ≃ {v : Fin k → 𝔽₂ // v ≠ 0} where
  toFun L := ⟨(finrank_one_exists_unique L).choose, (finrank_one_exists_unique L).choose_spec.1⟩
  invFun v := ⟨Submodule.span 𝔽₂ {v.1}, finrank_span_singleton v.2⟩
  left_inv L := by
    refine Subtype.ext ?_
    have hspec := (finrank_one_exists_unique L).choose_spec
    have h1 : Submodule.span 𝔽₂ {(finrank_one_exists_unique L).choose} ≤ L.1 :=
      Submodule.span_le.mpr (by simpa using hspec.2.1)
    exact Submodule.eq_of_le_of_finrank_eq h1 (by
      rw [finrank_span_singleton hspec.1, L.2])
  right_inv v := by
    refine Subtype.ext ?_
    have hspec := (finrank_one_exists_unique ⟨Submodule.span 𝔽₂ {v.1},
      finrank_span_singleton v.2⟩).choose_spec
    exact (hspec.2.2 v.1 (Submodule.subset_span (Set.mem_singleton _)) v.2).symm

/-- The Grassmannian of lines has `2^k - 1` elements. -/
lemma card_GrVertex_one (k : ℕ) : Fintype.card (GrVertex k 1) = 2 ^ k - 1 := by
  rw [Fintype.card_congr (lineEquivNonzero k), ← Nat.card_eq_fintype_card]
  rw [card_subtype_ne (0 : Fin k → 𝔽₂), natCard_fin_fun]

end

end F2
end Submission.Grassmann

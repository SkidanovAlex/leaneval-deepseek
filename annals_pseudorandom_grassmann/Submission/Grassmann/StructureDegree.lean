import Mathlib
import Submission.Grassmann.Hyperplane

/-!
# The degree of the structure functions `1_{A ≤ L ≤ B}`

The conclusion of the KMS theorem produces subspaces `A ≤ B` with `dim A + codim B ≤ r`.  The
"structure functions" of the argument are the indicators `1_{A ≤ L ≤ B}`; this file shows that
they are functions of **degree `≤ r`** on the Grassmann graph, i.e. they lie in `V_{dim A}`,
`V_{codim B}` and `V_{dim A + codim B}` respectively.

The two ingredients are

* `ind_sub_mem_Vup`: for a subspace `U` of dimension `u ≤ d ≤ ℓ`, the indicator
  `L ↦ [U ≤ L]` lies in `V_d` (via the Möbius-type identity
  `1_{U ≤ ·} = (1/[ℓ-u choose d-u]_2) ∑_{W ⊇ U, dim W = d} 1_{W ⊆ ·}`);
* `mul_mem_Vup`: `V_i · V_j ⊆ V_{i+j}` for `i + j ≤ ℓ`, because
  `1_{W ⊆ ·} · 1_{W' ⊆ ·} = 1_{W + W' ⊆ ·}` and `ind_sub_mem_Vup` handles `dim(W+W') ≤ i+j`.
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

lemma grCount_ne_zero {n m : ℕ} (h : m ≤ n) : grCount n m ≠ 0 := by
  rw [← card_GrVertex_eq_grCount]
  exact (Fintype.card_pos_iff.mpr (nonempty_GrVertex_of_le h)).ne'

lemma natCard_subtype_le_le (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (d : ℕ) :
    Nat.card {W : GrVertex k d // A ≤ W.1 ∧ W.1 ≤ B} = (SubGr k d A B).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, SubGr]

/-- **The "up" structure function has degree `≤ d`.**  For a subspace `U` of dimension at most
`d ≤ ℓ`, the indicator of `{L : U ≤ L}` lies in `V_d`. -/
theorem ind_sub_mem_Vup (U : Submodule 𝔽₂ (Fin k → 𝔽₂)) {d : ℕ}
    (hu : Module.finrank 𝔽₂ U ≤ d) (hd : d ≤ ℓ) :
    (fun L : GrVertex k ℓ => if U ≤ L.1 then (1 : ℚ) else 0) ∈ Vup (k := k) (ℓ := ℓ) d := by
  classical
  have hne : (grCount (ℓ - Module.finrank 𝔽₂ U) (d - Module.finrank 𝔽₂ U) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (grCount_ne_zero (by omega))
  refine ⟨fun W : GrVertex k d =>
    if U ≤ W.1 then (grCount (ℓ - Module.finrank 𝔽₂ U) (d - Module.finrank 𝔽₂ U) : ℚ)⁻¹
      else 0, ?_⟩
  funext L
  rw [upLM_apply, upFun]
  have hterm : ∀ W : GrVertex k d,
      (if W.1 ≤ L.1 then
        (if U ≤ W.1 then (grCount (ℓ - Module.finrank 𝔽₂ U) (d - Module.finrank 𝔽₂ U) : ℚ)⁻¹
          else 0) else 0)
      = (if U ≤ W.1 ∧ W.1 ≤ L.1 then
          (grCount (ℓ - Module.finrank 𝔽₂ U) (d - Module.finrank 𝔽₂ U) : ℚ)⁻¹ else 0) := by
    intro W
    by_cases h1 : W.1 ≤ L.1 <;> by_cases h2 : U ≤ W.1
    · rw [if_pos h1, if_pos h2, if_pos ⟨h2, h1⟩]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.1)]
    · rw [if_neg h1, if_neg (fun h => h1 h.2)]
    · rw [if_neg h1, if_neg (fun h => h1 h.2)]
  rw [Finset.sum_congr rfl (fun W _ => hterm W), ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  by_cases hUL : U ≤ L.1
  · rw [if_pos hUL]
    have hcard : (Finset.univ.filter (fun W : GrVertex k d => U ≤ W.1 ∧ W.1 ≤ L.1)).card
        = grCount (ℓ - Module.finrank 𝔽₂ U) (d - Module.finrank 𝔽₂ U) := by
      rw [← Fintype.card_subtype (fun W : GrVertex k d => U ≤ W.1 ∧ W.1 ≤ L.1),
        ← Nat.card_eq_fintype_card, natCard_subtype_le_le,
        card_SubGr_eq_grCount U L.1 hUL hu, L.2]
    rw [hcard]
    field_simp
  · rw [if_neg hUL]
    have hzero : (Finset.univ.filter (fun W : GrVertex k d => U ≤ W.1 ∧ W.1 ≤ L.1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro W _
      exact fun h => hUL (le_trans h.1 h.2)
    rw [hzero, Nat.cast_zero, zero_mul]

/-- **The product rule for the degree filtration**: `V_i · V_j ⊆ V_{i+j}` (for `i + j ≤ ℓ`). -/
theorem mul_mem_Vup {i j : ℕ} (hij : i + j ≤ ℓ) {f g : GrVertex k ℓ → ℚ}
    (hf : f ∈ Vup (k := k) (ℓ := ℓ) i) (hg : g ∈ Vup (k := k) (ℓ := ℓ) j) :
    (fun L => f L * g L) ∈ Vup (k := k) (ℓ := ℓ) (i + j) := by
  classical
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  simp only [upLM_apply]
  have hexp : ∀ L : GrVertex k ℓ, upFun i a L * upFun j b L
      = ∑ W : GrVertex k i, ∑ W' : GrVertex k j,
          (a W * b W') * (if (W.1 ⊔ W'.1) ≤ L.1 then (1 : ℚ) else 0) := by
    intro L
    rw [upFun, upFun, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun W _ => Finset.sum_congr rfl (fun W' _ => ?_))
    by_cases hW : W.1 ≤ L.1 <;> by_cases hW' : W'.1 ≤ L.1
    · rw [if_pos hW, if_pos hW', if_pos (sup_le hW hW')]
      ring
    · rw [if_pos hW, if_neg hW', if_neg (fun h => hW' (le_trans le_sup_right h))]
      ring
    · rw [if_neg hW, if_neg (fun h => hW (le_trans le_sup_left h))]
      ring
    · rw [if_neg hW, if_neg (fun h => hW (le_trans le_sup_left h))]
      ring
  have hfun : (fun L => upFun i a L * upFun j b L)
      = ∑ W : GrVertex k i, ∑ W' : GrVertex k j,
          (a W * b W') • (fun L : GrVertex k ℓ =>
            if (W.1 ⊔ W'.1) ≤ L.1 then (1 : ℚ) else 0) := by
    funext L
    rw [hexp L]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  refine Submodule.sum_mem _ (fun W _ => Submodule.sum_mem _ (fun W' _ => ?_))
  refine Submodule.smul_mem _ _ (ind_sub_mem_Vup (W.1 ⊔ W'.1) ?_ hij)
  have h := Submodule.finrank_sup_add_finrank_inf_eq W.1 W'.1
  rw [W.2, W'.2] at h
  omega

/-- Every proper subspace of `𝔽₂ᵏ` is contained in a hyperplane. -/
lemma exists_hyperplane_ge (B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hne : B ≠ ⊤) :
    ∃ H : Submodule 𝔽₂ (Fin k → 𝔽₂), B ≤ H ∧ Module.finrank 𝔽₂ H = k - 1 := by
  have hbot : B.dualAnnihilator ≠ ⊥ := by
    intro h
    apply hne
    have h1 : B.dualAnnihilator.dualCoannihilator = ⊤ := by rw [h]; simp
    rwa [Subspace.dualAnnihilator_dualCoannihilator_eq] at h1
  obtain ⟨φ, hφmem, hφne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  refine ⟨LinearMap.ker φ, ?_, ?_⟩
  · intro x hx
    rw [LinearMap.mem_ker]
    exact (Submodule.mem_dualAnnihilator φ).mp hφmem x hx
  · have h := finrank_ker_eq_pred (V := Fin k → 𝔽₂) φ hφne
    rwa [finrank_fin_fun] at h

/-- **The "down" structure function has degree `≤ codim`.**  For a subspace `B` with
`codim B = b ≤ ℓ`, the indicator of `{L : L ≤ B}` lies in `V_b`. -/
theorem ind_le_mem_Vup (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    ∀ b ≤ ℓ, ∀ B : Submodule 𝔽₂ (Fin k → 𝔽₂), Module.finrank 𝔽₂ B = k - b →
      (fun L : GrVertex k ℓ => if L.1 ≤ B then (1 : ℚ) else 0)
        ∈ Vup (k := k) (ℓ := ℓ) b := by
  intro b
  induction b with
  | zero =>
    intro _ B hB
    have htop : B = ⊤ := Submodule.eq_top_of_finrank_eq (by
      rw [hB, Nat.sub_zero, finrank_fin_fun])
    subst htop
    have hconst : (fun L : GrVertex k ℓ =>
        if L.1 ≤ (⊤ : Submodule 𝔽₂ (Fin k → 𝔽₂)) then (1 : ℚ) else 0)
        = (fun _ : GrVertex k ℓ => (1 : ℚ)) := by
      funext L; simp
    rw [hconst]
    exact const_mem_Vup_zero 1
  | succ b ih =>
    intro hb B hB
    have hbk : b ≤ ℓ := by omega
    have hBlt : Module.finrank 𝔽₂ B < k := by
      have h := Submodule.finrank_le B
      rw [finrank_fin_fun] at h
      omega
    have hne : B ≠ ⊤ := by
      intro h
      rw [h, finrank_top_eq_k] at hBlt
      omega
    obtain ⟨H, hBH, hHfr⟩ := exists_hyperplane_ge B hne
    have hHtop : H ≠ ⊤ := by
      intro h
      rw [h, finrank_top_eq_k] at hHfr
      omega
    obtain ⟨v, hvH⟩ : ∃ v : Fin k → 𝔽₂, v ∉ H := by
      by_contra h
      push_neg at h
      exact hHtop (Submodule.eq_top_iff'.mpr h)
    have hvB : v ∉ B := fun h => hvH (hBH h)
    have hv0 : v ≠ 0 := fun h => hvB (h ▸ B.zero_mem)
    set B' : Submodule 𝔽₂ (Fin k → 𝔽₂) := B ⊔ Submodule.span 𝔽₂ {v} with hB'def
    have hB'fr : Module.finrank 𝔽₂ B' = k - b := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq B (Submodule.span 𝔽₂ {v})
      have hspan : Module.finrank 𝔽₂ ↥(Submodule.span 𝔽₂ {v}) = 1 :=
        finrank_span_singleton hv0
      have hinf : Module.finrank 𝔽₂ ↥(B ⊓ Submodule.span 𝔽₂ {v}) = 0 := by
        rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
        intro x hx
        rw [Submodule.mem_inf] at hx
        obtain ⟨hxB, hxspan⟩ := hx
        rw [Submodule.mem_span_singleton] at hxspan
        obtain ⟨c, hc⟩ := hxspan
        rcases eq_or_ne c 0 with hc0 | hc0
        · rw [hc0, zero_smul] at hc
          exact hc.symm
        · rw [zmod2_eq_one hc0, one_smul] at hc
          exact absurd (hc ▸ hxB) hvB
      rw [hspan, hinf, add_zero] at h
      rw [hB'def]
      omega
    have hHB : H ⊓ B' = B := by
      refine le_antisymm ?_ (le_inf hBH le_sup_left)
      intro x hx
      rw [Submodule.mem_inf] at hx
      obtain ⟨hxH, hxB'⟩ := hx
      rw [hB'def, Submodule.mem_sup] at hxB'
      obtain ⟨β, hβ, z, hz, hβz⟩ := hxB'
      rw [Submodule.mem_span_singleton] at hz
      obtain ⟨c, hc⟩ := hz
      have hzH : z ∈ H := by
        have hzx : z = x - β := by rw [← hβz]; abel
        rw [hzx]; exact Submodule.sub_mem _ hxH (hBH hβ)
      rcases eq_or_ne c 0 with hc0 | hc0
      · rw [hc0, zero_smul] at hc
        rw [← hβz, ← hc, add_zero]; exact hβ
      · exfalso
        rw [zmod2_eq_one hc0, one_smul] at hc
        exact hvH (hc ▸ hzH)
    have hfun : (fun L : GrVertex k ℓ => if L.1 ≤ B then (1 : ℚ) else 0)
        = (fun L : GrVertex k ℓ =>
            (if L.1 ≤ B' then (1 : ℚ) else 0) * (if L.1 ≤ H then (1 : ℚ) else 0)) := by
      funext L
      rw [← hHB]
      by_cases h1 : L.1 ≤ H <;> by_cases h2 : L.1 ≤ B'
      · rw [if_pos h1, if_pos h2, if_pos (le_inf h1 h2), mul_one]
      · rw [if_pos h1, if_neg h2,
          if_neg (fun h => h2 (fun x hx => (h hx).2)), zero_mul]
      · rw [if_neg h1, if_pos h2,
          if_neg (fun h => h1 (fun x hx => (h hx).1)), mul_zero]
      · rw [if_neg h1, if_neg h2,
          if_neg (fun h => h1 (fun x hx => (h hx).1)), zero_mul]
    rw [hfun]
    exact mul_mem_Vup (k := k) (ℓ := ℓ) (i := b) (j := 1) (by omega)
      (ih hbk B' hB'fr) (hyperplaneInd_mem_Vup hℓ H hHfr)

/-- Version of `ind_le_mem_Vup` phrased with `codim`: for `codim B ≤ ℓ`,
`(L ↦ [L ≤ B]) ∈ V_{codim B}`. -/
theorem ind_le_mem_Vup' (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) (B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (hb : k - Module.finrank 𝔽₂ B ≤ ℓ) :
    (fun L : GrVertex k ℓ => if L.1 ≤ B then (1 : ℚ) else 0)
      ∈ Vup (k := k) (ℓ := ℓ) (k - Module.finrank 𝔽₂ B) := by
  refine ind_le_mem_Vup hℓ hk _ hb B ?_
  have h := Submodule.finrank_le B
  rw [finrank_fin_fun] at h
  omega

/-- **The structure functions have degree `≤ dim A + codim B`.**  For subspaces `A ≤ B` with
`dim A + (k - dim B) ≤ ℓ`, the indicator of the sub-Grassmannian `Gr[A,B]` lies in
`V_{dim A + codim B}` — this is the precise sense in which the "defect" `dim A + codim B`
controls the Fourier degree of the structure appearing in the KMS theorem. -/
theorem structInd_mem_Vup (hℓ : 1 ≤ ℓ) (hk : ℓ ≤ k) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂))
    (ha : Module.finrank 𝔽₂ A ≤ ℓ) (hb : k - Module.finrank 𝔽₂ B ≤ ℓ)
    (hab : Module.finrank 𝔽₂ A + (k - Module.finrank 𝔽₂ B) ≤ ℓ) :
    (fun L : GrVertex k ℓ => if A ≤ L.1 ∧ L.1 ≤ B then (1 : ℚ) else 0)
      ∈ Vup (k := k) (ℓ := ℓ) (Module.finrank 𝔽₂ A + (k - Module.finrank 𝔽₂ B)) := by
  have h1 : (fun L : GrVertex k ℓ => if A ≤ L.1 then (1 : ℚ) else 0)
      ∈ Vup (k := k) (ℓ := ℓ) (Module.finrank 𝔽₂ A) :=
    ind_sub_mem_Vup A le_rfl ha
  have h2 : (fun L : GrVertex k ℓ => if L.1 ≤ B then (1 : ℚ) else 0)
      ∈ Vup (k := k) (ℓ := ℓ) (k - Module.finrank 𝔽₂ B) :=
    ind_le_mem_Vup' hℓ hk B hb
  have hprod := mul_mem_Vup (k := k) (ℓ := ℓ)
    (i := Module.finrank 𝔽₂ A) (j := k - Module.finrank 𝔽₂ B) hab h1 h2
  have hfun : (fun L : GrVertex k ℓ => if A ≤ L.1 ∧ L.1 ≤ B then (1 : ℚ) else 0)
      = (fun L : GrVertex k ℓ =>
          (if A ≤ L.1 then (1 : ℚ) else 0) * (if L.1 ≤ B then (1 : ℚ) else 0)) := by
    funext L
    by_cases h1 : A ≤ L.1 <;> by_cases h2 : L.1 ≤ B
    · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, mul_one]
    · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2), mul_zero]
    · rw [if_neg h1, if_neg (fun h => h1 h.1), zero_mul]
    · rw [if_neg h1, if_neg (fun h => h1 h.1), zero_mul]
  rw [hfun]
  exact hprod

end

end F2
end Submission.Grassmann

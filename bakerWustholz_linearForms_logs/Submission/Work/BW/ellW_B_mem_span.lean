import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.ker_orth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Linear-algebra core of the `multiplicity_prop` case analysis

This file proves `Work.BW.ellW_B_mem_span`, together with the (private) auxiliary
linear-algebra lemmas it uses: the dimension of the span of the operator family `w`, the
dimension of `lieSub`, the resulting inclusion `lieSub ≤ span (range w)`, and the projection
step extracting `ker M ⊆ span c` from it.
-/

namespace Work.BW

open Complex

section Aux

variable {r ρ : ℕ}

/-- The matrix attached to `M`, with entries cast to `ℂ`. -/
private noncomputable def auxMat (M : Fin ρ → Fin r → ℤ) : Matrix (Fin ρ) (Fin r) ℂ :=
  Matrix.of fun j i => (((M j i : ℤ) : ℚ) : ℂ)

/-- The matrix `M` (rows indexed by `Fin ρ`, columns by `Fin r`) as the `ℂ`-linear map
`v ↦ (∑ᵢ M_{ji} vᵢ)_j`. -/
private noncomputable def auxMv (M : Fin ρ → Fin r → ℤ) : (Fin r → ℂ) →ₗ[ℂ] (Fin ρ → ℂ) :=
  (auxMat M).mulVecLin

private lemma auxMv_apply (M : Fin ρ → Fin r → ℤ) (v : Fin r → ℂ) (j : Fin ρ) :
    auxMv M v j = ∑ i, (((M j i : ℤ) : ℚ) : ℂ) * v i := by
  simp only [auxMv, Matrix.mulVecLin_apply, Matrix.mulVec_apply_eq_sum, auxMat, Matrix.of_apply]

/-- The two ways of casting `n : ℤ` to `ℂ` agree. -/
private lemma aux_cast (n : ℤ) : (((n : ℤ) : ℚ) : ℂ) = ((n : ℂ)) := by simp

/-- `∑` commutes with the cast `ℚ → ℂ`. -/
private lemma aux_cast_sum {ι : Type*} [Fintype ι] (f : ι → ℚ) :
    (((∑ i, f i : ℚ)) : ℂ) = ∑ i, ((f i : ℚ) : ℂ) := by
  push_cast
  rfl

/-- The projection `v ↦ (v_{i+1})_i`. -/
private def auxTail (r : ℕ) : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin r → ℂ) where
  toFun v := fun i => v i.succ
  map_add' x y := by funext i; rfl
  map_smul' a x := by funext i; rfl

@[simp] private lemma auxTail_apply (r : ℕ) (v : Fin (r + 1) → ℂ) (i : Fin r) :
    auxTail r v i = v i.succ := rfl

@[simp] private lemma auxTail_cons (r : ℕ) (c : ℂ) (u : Fin r → ℂ) :
    auxTail r (Fin.cons c u) = u := by
  funext i; simp

@[simp] private lemma auxTail_single (r : ℕ) (z : ℂ) :
    auxTail r (Pi.single (0 : Fin (r + 1)) z) = 0 := by
  funext i
  simp only [auxTail_apply, Pi.zero_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero i)]

private lemma auxTail_surj (r : ℕ) : Function.Surjective (auxTail r) :=
  fun v => ⟨Fin.cons 0 v, auxTail_cons r 0 v⟩

private lemma aux_projsum_cast (M : Fin ρ → Fin r → ℤ) (j : Fin ρ) :
    (∑ i : Fin r, (((M j i : ℤ) : ℚ) : ℂ) •
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.succ)
      = (∑ i : Fin r, ((M j i : ℂ)) •
        LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.succ) := by
  apply Finset.sum_congr rfl
  intro i _
  rw [aux_cast]

/-- The `ρ` linear conditions cutting out `lieSub` coincide with the kernel of the composite
`auxMv M ∘ auxTail r`. -/
private lemma aux_iInf_ker_eq (M : Fin ρ → Fin r → ℤ) :
    (⨅ j : Fin ρ, LinearMap.ker
        (∑ i : Fin r, ((M j i : ℂ)) •
          LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.succ))
      = LinearMap.ker ((auxMv M).comp (auxTail r)) := by
  simp only [← aux_projsum_cast M]
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
  have h : ∀ j : Fin ρ,
      ((∑ i : Fin r, (((M j i : ℤ) : ℚ) : ℂ) •
          LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) i.succ) v)
        = (auxMv M) ((auxTail r) v) j := by
    intro j
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul, auxMv_apply, auxTail_apply]
  constructor
  · intro hv
    funext j
    rw [← h j]
    exact hv j
  · intro hv j
    rw [h j]
    exact congrFun hv j

/-- `auxMv M` is surjective when the rows of `M` are `ℂ`-linearly independent. -/
private lemma auxMv_range_eq_top (M : Fin ρ → Fin r → ℤ)
    (hM : LinearIndependent ℂ (fun j : Fin ρ => fun i : Fin r => (((M j i : ℤ) : ℚ) : ℂ))) :
    LinearMap.range (auxMv M) = ⊤ := by
  have h : (auxMv M) = (auxMat M).mulVecLin := by simp only [auxMv]
  rw [h]
  refine Submodule.eq_top_of_finrank_eq ?_
  change (auxMat M).rank = Module.finrank ℂ (Fin ρ → ℂ)
  have hli : LinearIndependent ℂ (auxMat M).row := hM
  rw [LinearIndependent.rank_matrix hli, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The kernel of `auxMv M ∘ auxTail r` has dimension `r + 1 - ρ`. -/
private lemma aux_finrank_ker_comp (M : Fin ρ → Fin r → ℤ)
    (hM : LinearIndependent ℂ (fun j : Fin ρ => fun i : Fin r => (((M j i : ℤ) : ℚ) : ℂ))) :
    Module.finrank ℂ (LinearMap.ker ((auxMv M).comp (auxTail r))) = r + 1 - ρ := by
  have h := LinearMap.finrank_range_add_finrank_ker ((auxMv M).comp (auxTail r))
  have htop : LinearMap.range ((auxMv M).comp (auxTail r)) = ⊤ := by
    rw [LinearMap.range_comp, (LinearMap.range_eq_top).mpr (auxTail_surj r), Submodule.map_top,
      auxMv_range_eq_top M hM]
  rw [htop] at h
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  omega

/-- The kernel of `proj 0 : ℂ^{r+1} → ℂ` has dimension `r`. -/
private lemma aux_finrank_ker_proj (r : ℕ) :
    Module.finrank ℂ (LinearMap.ker
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0)) = r := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0 : (Fin (r + 1) → ℂ) →ₗ[ℂ] ℂ)
  have htop : LinearMap.range
      (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0 :
        (Fin (r + 1) → ℂ) →ₗ[ℂ] ℂ) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro c
    exact ⟨Pi.single (0 : Fin (r + 1)) c, by simp [LinearMap.proj_apply]⟩
  rw [htop] at h
  simp only [finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h
  omega

/-- Unfolded description of `lieSub`. -/
private lemma aux_lieSub_unfold (M : Fin ρ → Fin r → ℤ) (ε : Bool) :
    lieSub r ρ ε M = (if ε then ⊤ else LinearMap.ker
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0))
      ⊓ LinearMap.ker ((auxMv M).comp (auxTail r)) := by
  simp only [lieSub, aux_iInf_ker_eq M]

private lemma aux_lieSub_true (M : Fin ρ → Fin r → ℤ) :
    lieSub r ρ true M = LinearMap.ker ((auxMv M).comp (auxTail r)) := by
  rw [aux_lieSub_unfold M true]
  simp

private lemma aux_lieSub_false (M : Fin ρ → Fin r → ℤ) :
    lieSub r ρ false M = LinearMap.ker
        (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0)
      ⊓ LinearMap.ker ((auxMv M).comp (auxTail r)) := by
  rw [aux_lieSub_unfold M false]
  simp

private lemma aux_finrank_lieSub_true (hρ : 1 ≤ ρ) (M : Fin ρ → Fin r → ℤ)
    (hM : LinearIndependent ℂ (fun j : Fin ρ => fun i : Fin r => (((M j i : ℤ) : ℚ) : ℂ))) :
    Module.finrank ℂ (lieSub r ρ true M) = r - (ρ - 1) := by
  rw [aux_lieSub_true M, aux_finrank_ker_comp M hM]
  omega

private lemma aux_finrank_lieSub_false (hρr : ρ ≤ r) (M : Fin ρ → Fin r → ℤ)
    (hM : LinearIndependent ℂ (fun j : Fin ρ => fun i : Fin r => (((M j i : ℤ) : ℚ) : ℂ))) :
    Module.finrank ℂ (lieSub r ρ false M) = r - ρ := by
  have hP := aux_finrank_ker_comp M hM
  have hQ := aux_finrank_ker_proj r
  rw [aux_lieSub_false M]
  have hsup : LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0)
      ⊔ LinearMap.ker ((auxMv M).comp (auxTail r)) = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro v
    refine Submodule.mem_sup.mpr ⟨v - (v 0) • Pi.single (0 : Fin (r + 1)) (1 : ℂ), ?_,
      (v 0) • Pi.single (0 : Fin (r + 1)) (1 : ℂ), ?_, by abel⟩
    · rw [LinearMap.mem_ker, LinearMap.proj_apply]
      simp
    · rw [LinearMap.mem_ker, LinearMap.comp_apply, map_smul, auxTail_single, smul_zero, map_zero]
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.ker (LinearMap.proj (R := ℂ) (φ := fun _ : Fin (r + 1) => ℂ) 0))
    (LinearMap.ker ((auxMv M).comp (auxTail r)))
  rw [hsup, hQ, hP] at hdim
  simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
  omega

private lemma aux_lieSub_le_span (M : Fin ρ → Fin r → ℤ) (ε : Bool)
    (w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ)
    (hW : Module.finrank ℂ (Submodule.span ℂ (Set.range w)) = r)
    (hL : Module.finrank ℂ (lieSub r ρ ε M) = r - ((if ε then ρ else ρ + 1) - 1))
    (hℓ : ellW (N := r) (q := r - 1 + 1) w ε M = (if ε then ρ else ρ + 1) - 1) :
    lieSub r ρ ε M ≤ Submodule.span ℂ (Set.range w) := by
  have hℓu : Module.finrank ℂ (Submodule.span ℂ (Set.range w)) -
      Module.finrank ℂ ((Submodule.span ℂ (Set.range w) ⊓ lieSub r ρ ε M :
        Submodule ℂ (Fin (r + 1) → ℂ)))
      = (if ε then ρ else ρ + 1) - 1 := hℓ
  rw [hW] at hℓu
  have hle : Module.finrank ℂ ((Submodule.span ℂ (Set.range w) ⊓ lieSub r ρ ε M :
      Submodule ℂ (Fin (r + 1) → ℂ))) ≤ r :=
    (Submodule.finrank_mono inf_le_left).trans_eq hW
  have hk : Module.finrank ℂ ((Submodule.span ℂ (Set.range w) ⊓ lieSub r ρ ε M :
      Submodule ℂ (Fin (r + 1) → ℂ))) = r - ((if ε then ρ else ρ + 1) - 1) := by omega
  have heq : (Submodule.span ℂ (Set.range w) ⊓ lieSub r ρ ε M :
      Submodule ℂ (Fin (r + 1) → ℂ)) = lieSub r ρ ε M :=
    Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [hk, hL])
  rw [← heq]
  exact inf_le_left

/-- Linear independence of the operator family `w` (`e₀` together with the `(0, c_m)`). -/
private lemma aux_w_linearIndependent {r : ℕ} (c : Fin (r - 1) → Fin r → ℚ)
    (hc : LinearIndependent ℂ (fun m : Fin (r - 1) => fun i : Fin r => ((c m i : ℚ) : ℂ)))
    (w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ)
    (hw0 : w 0 = Pi.single (0 : Fin (r + 1)) (1 : ℂ))
    (hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) :
    LinearIndependent ℂ w := by
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have h0 : a 0 = 0 := by
    have h := congrFun ha 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [Fin.sum_univ_succ] at h
    have hz : (∑ m : Fin (r - 1), a m.succ * w m.succ 0) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      rw [hw1 m, Fin.cons_zero, mul_zero]
    rw [hz, add_zero, hw0, Pi.single_eq_same, mul_one] at h
    exact h
  have hkey : ∀ j : Fin r, ∑ m : Fin (r - 1), a m.succ * ((c m j : ℚ) : ℂ) = 0 := by
    intro j
    have h := congrFun ha j.succ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [Fin.sum_univ_succ, h0] at h
    simp only [zero_mul, zero_add] at h
    have hc' : (∑ m : Fin (r - 1), a m.succ * w m.succ j.succ)
        = ∑ m : Fin (r - 1), a m.succ * ((c m j : ℚ) : ℂ) :=
      Finset.sum_congr rfl fun m _ => by rw [hw1 m, Fin.cons_succ]
    rwa [hc'] at h
  have hs : (∑ m : Fin (r - 1),
      a m.succ • (fun i : Fin r => ((c m i : ℚ) : ℂ))) = 0 := by
    funext j
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hkey j
  have hzer : (fun m : Fin (r - 1) => a m.succ) = 0 := by
    funext m
    exact (Fintype.linearIndependent_iff.mp hc) (fun m : Fin (r - 1) => a m.succ) hs m
  intro i
  by_cases hi : i = 0
  · rw [hi]; exact h0
  · obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hi
    rw [← hk]
    exact congrFun hzer k

/-- The family `w` spans an `r`-dimensional space. -/
private lemma aux_finrank_span_w {r : ℕ} (hr : 1 ≤ r) (c : Fin (r - 1) → Fin r → ℚ)
    (hc : LinearIndependent ℂ (fun m : Fin (r - 1) => fun i : Fin r => ((c m i : ℚ) : ℂ)))
    (w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ)
    (hw0 : w 0 = Pi.single (0 : Fin (r + 1)) (1 : ℂ))
    (hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ))) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range w)) = r := by
  rw [finrank_span_eq_card (aux_w_linearIndependent c hc w hw0 hw1), Fintype.card_fin,
    Nat.sub_add_cancel hr]

private lemma aux_cons_mem_lieSub_true (M : Fin ρ → Fin r → ℤ) (u : Fin r → ℂ)
    (hu : (auxMv M) u = 0) :
    (Fin.cons (0 : ℂ) u : Fin (r + 1) → ℂ) ∈ lieSub r ρ true M := by
  rw [aux_lieSub_true M]
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, auxTail_cons]
  exact hu

private lemma aux_cons_mem_lieSub_false (M : Fin ρ → Fin r → ℤ) (u : Fin r → ℂ)
    (hu : (auxMv M) u = 0) :
    (Fin.cons (0 : ℂ) u : Fin (r + 1) → ℂ) ∈ lieSub r ρ false M := by
  rw [aux_lieSub_false M, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · simp only [LinearMap.mem_ker, LinearMap.proj_apply]
    simp only [Fin.cons_zero]
  · simp only [LinearMap.mem_ker, LinearMap.comp_apply, auxTail_cons]
    exact hu

private lemma aux_cons_mem_lieSub (M : Fin ρ → Fin r → ℤ) (ε : Bool) (u : Fin r → ℂ)
    (hu : (auxMv M) u = 0) :
    (Fin.cons (0 : ℂ) u : Fin (r + 1) → ℂ) ∈ lieSub r ρ ε M := by
  cases ε with
  | false => exact aux_cons_mem_lieSub_false M u hu
  | true => exact aux_cons_mem_lieSub_true M u hu

end Aux

/-- Linear-algebra core of the `multiplicity_prop` case analysis (BW §10, P86* route). Let the
`c m : Fin r → ℚ` be `ℚ`-independent, let `M : Fin ρ → Fin r → ℤ` have `ℚ`-independent rows, let
`B : Fin r → ℤ` be non-zero and orthogonal to every `c m`, and let `w : Fin (r-1+1) → Fin (r+1) → ℂ`
be the operator family `w 0 = e₀`, `w m.succ = Fin.cons 0 (fun i => c m i)`. If the zero estimate
returns the subgroup `G' = G_a^ε × ker 𝒵` at the transferable codimension, i.e.
`ellW w ε M = (if ε then ρ else ρ+1) - 1`, then `B` lies in the `ℚ`-span of the rows of `M`. -/
theorem ellW_B_mem_span {r ρ : ℕ} (hr : 2 ≤ r) (hρ : 1 ≤ ρ) (hρr : ρ ≤ r)
    (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ (fun m i => (c m i : ℚ)))
    (M : Fin ρ → Fin r → ℤ) (hM : LinearIndependent ℚ (fun j i => (M j i : ℚ)))
    (B : Fin r → ℤ) (hB : B ≠ 0) (hcB : ∀ m, ∑ i, (c m i) * (B i : ℚ) = 0)
    (ε : Bool) (w : Fin (r - 1 + 1) → Fin (r + 1) → ℂ)
    (hw0 : w 0 = Pi.single (0 : Fin (r + 1)) (1 : ℂ))
    (hw1 : ∀ m : Fin (r - 1), w m.succ = Fin.cons 0 (fun i : Fin r => ((c m i : ℚ) : ℂ)))
    (hℓ : ellW (N := r) (q := r - 1 + 1) w ε M = (if ε then ρ else ρ + 1) - 1) :
    (fun i => (B i : ℚ)) ∈ Submodule.span ℚ (Set.range fun j i => (M j i : ℚ)) := by
  classical
  have hr1 : 1 ≤ r := by omega
  -- `ℂ`-forms of the independence hypotheses.
  have hcℂ : LinearIndependent ℂ (fun m : Fin (r - 1) => fun i : Fin r => ((c m i : ℚ) : ℂ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
      (v := fun m : Fin (r - 1) => fun i : Fin r => c m i)).mpr hc
  have hMℂ : LinearIndependent ℂ
      (fun j : Fin ρ => fun i : Fin r => (((M j i : ℤ) : ℚ) : ℂ)) :=
    (linearIndependent_algebraMap_comp_iff (R := ℚ) (S := ℂ)
      (v := fun j : Fin ρ => fun i : Fin r => ((M j i : ℤ) : ℚ))).mpr hM
  -- Dimension of `span (range w)`.
  have hW : Module.finrank ℂ (Submodule.span ℂ (Set.range w)) = r :=
    aux_finrank_span_w hr1 c hcℂ w hw0 hw1
  -- `lieSub ≤ span (range w)`.
  have hLW : lieSub r ρ ε M ≤ Submodule.span ℂ (Set.range w) := by
    cases ε with
    | false =>
      exact aux_lieSub_le_span M false w hW
        (by simpa using aux_finrank_lieSub_false hρr M hMℂ) hℓ
    | true =>
      exact aux_lieSub_le_span M true w hW
        (by simpa using aux_finrank_lieSub_true hρ M hMℂ) hℓ
  -- Projection step: `ker M ⊆ span c`.
  have hker : ∀ u : Fin r → ℂ, (auxMv M) u = 0 →
      u ∈ Submodule.span ℂ
        (Set.range (fun m : Fin (r - 1) => fun i : Fin r => ((c m i : ℚ) : ℂ))) := by
    intro u hu
    have hmem : (Fin.cons (0 : ℂ) u : Fin (r + 1) → ℂ) ∈ lieSub r ρ ε M :=
      aux_cons_mem_lieSub M ε u hu
    have hWmem : (Fin.cons (0 : ℂ) u : Fin (r + 1) → ℂ) ∈ Submodule.span ℂ (Set.range w) :=
      hLW hmem
    have hmap : u ∈ Submodule.map (auxTail r) (Submodule.span ℂ (Set.range w)) :=
      ⟨Fin.cons 0 u, hWmem, auxTail_cons r 0 u⟩
    rw [Submodule.map_span] at hmap
    refine Submodule.span_le.mpr ?_ hmap
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    by_cases hi : i = 0
    · subst hi
      rw [hw0, auxTail_single]
      exact Submodule.zero_mem _
    · obtain ⟨k, hk⟩ := Fin.exists_succ_eq_of_ne_zero hi
      rw [← hk, hw1 k, auxTail_cons]
      exact Submodule.subset_span (Set.mem_range_self k)
  -- Final step: `ker_orth` and the orthogonality of `B` with the rows of `c`.
  by_contra hcon
  obtain ⟨wq, hwqker, hwqB⟩ :=
    ker_orth (A := fun j : Fin ρ => fun i : Fin r => ((M j i : ℤ) : ℚ))
      (u := fun i : Fin r => ((B i : ℤ) : ℚ)) hcon
  have hwqC : (fun i : Fin r => ((wq i : ℚ) : ℂ)) ∈
      Submodule.span ℂ
        (Set.range (fun m : Fin (r - 1) => fun i : Fin r => ((c m i : ℚ) : ℂ))) := by
    apply hker
    funext j
    rw [auxMv_apply]
    have hcast : (∑ i : Fin r, (((M j i : ℤ) : ℚ) : ℂ) * ((wq i : ℚ) : ℂ))
        = ((∑ i : Fin r, ((M j i : ℚ)) * wq i : ℚ) : ℂ) := by
      rw [aux_cast_sum (fun i : Fin r => ((M j i : ℚ)) * wq i)]
      exact Finset.sum_congr rfl fun i _ => by rw [Rat.cast_mul]
    rw [hcast, hwqker j]
    norm_num
  obtain ⟨lam, hlam⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwqC
  have hfun : ∀ i : Fin r, ((wq i : ℚ) : ℂ)
      = ∑ m : Fin (r - 1), lam m * ((c m i : ℚ) : ℂ) := by
    intro i
    have h := congrFun hlam i
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm
  have hzero : (∑ i : Fin r, ((B i : ℚ) : ℂ) * ((wq i : ℚ) : ℂ)) = 0 := by
    calc ∑ i : Fin r, ((B i : ℚ) : ℂ) * ((wq i : ℚ) : ℂ)
        = ∑ i : Fin r, ((B i : ℚ) : ℂ) *
            (∑ m : Fin (r - 1), lam m * ((c m i : ℚ) : ℂ)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hfun i]
      _ = ∑ m : Fin (r - 1), lam m *
            (∑ i : Fin r, ((B i : ℚ) : ℂ) * ((c m i : ℚ) : ℂ)) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro m _
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = 0 := by
          apply Finset.sum_eq_zero
          intro m _
          have hcBm : (∑ i : Fin r, ((B i : ℚ) : ℂ) * ((c m i : ℚ) : ℂ)) = 0 := by
            have hq : (∑ i : Fin r, (B i : ℚ) * (c m i)) = 0 := by
              rw [← hcB m]
              exact Finset.sum_congr rfl fun i _ => by ring
            calc (∑ i : Fin r, ((B i : ℚ) : ℂ) * ((c m i : ℚ) : ℂ))
                = ((∑ i : Fin r, (B i : ℚ) * (c m i) : ℚ) : ℂ) := by
                  rw [aux_cast_sum (fun i : Fin r => (B i : ℚ) * (c m i))]
                  exact Finset.sum_congr rfl fun i _ => by rw [Rat.cast_mul]
              _ = 0 := by rw [hq]; norm_num
          rw [hcBm, mul_zero]
  have hfinQ : (∑ i : Fin r, (B i : ℚ) * wq i) = 0 :=
    Rat.cast_injective (by
      rw [aux_cast_sum (fun i : Fin r => (B i : ℚ) * wq i), Rat.cast_zero, ← hzero]
      exact Finset.sum_congr rfl fun i _ => by rw [Rat.cast_mul])
  exact hwqB hfinQ

end Work.BW

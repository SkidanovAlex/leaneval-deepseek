import Mathlib
import Submission.Work.Lattice.Lemma5Second

/-!
# One-step orthonormal extension keeping the `π₊`-cone condition (Prop 5, induction step)

`Lemma5Second.lemma5_second_assertion` extends a family `w` (with a large `π₊`-wedge ratio)
by *one* further vector taken from an orthonormal family `u` of a subspace.  For the block
induction of Prop 5 the extension vector must be orthogonal to the already constructed family
and must keep the `π₊`-wedge *on the orthonormal side* (so that the induction can continue).

This module provides that: given an orthonormal `e : Fin m → ℝᵈ` with a large `π₊`-wedge and an
orthonormal `u : Fin i → ℝᵈ` inside a subspace `W` containing `e` with
`ε ≤ ‖⋀^i P (u₁∧…∧u_i)‖`, there is a unit vector `u' ∈ W`, orthogonal to `e_1,…,e_m`, with
`ε γ ≤ ‖π₊(e₁∧…∧e_m∧u')‖` (`γ` as in the second assertion).
-/

noncomputable section
open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Submission.Lemma5Extension

open Submission.ExteriorCoordinates
open Submission.WedgeProjection

variable {d : ℕ}

/-- `Fin.snoc` commutes with post-composition. -/
lemma snoc_comp {α β : Type*} {m : ℕ} (g : α → β) (e : Fin m → α) (x : α) :
    Fin.snoc (α := fun _ : Fin (m + 1) => β) (fun j : Fin m => g (e j)) (g x) = g ∘ Fin.snoc e x := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Function.comp_apply, Fin.snoc_castSucc]
  · rw [Fin.snoc_last, Function.comp_apply, Fin.snoc_last]

/-- `ιMulti` is linear in the last slot of `Fin.snoc` (subtraction form). -/
lemma iMulti_snoc_sub {d r : ℕ} (u : Fin r → RD d) (x y : RD d) :
    exteriorPower.ιMulti ℝ (r + 1) (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u (x - y)) =
      exteriorPower.ιMulti ℝ (r + 1) (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u x) -
        exteriorPower.ιMulti ℝ (r + 1) (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u y) := by
  have h := AlternatingMap.map_update_sub (exteriorPower.ιMulti ℝ (r + 1))
    (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u (0 : RD d)) (Fin.last r) x y
  simpa only [← snoc_eq_update] using h

/-- `ιMulti` is linear in the last slot of `Fin.snoc` (scalar form). -/
lemma iMulti_snoc_smul {d r : ℕ} (u : Fin r → RD d) (a : ℝ) (x : RD d) :
    exteriorPower.ιMulti ℝ (r + 1) (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u (a • x)) =
      a • exteriorPower.ιMulti ℝ (r + 1) (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u x) := by
  have h := AlternatingMap.map_update_smul (exteriorPower.ιMulti ℝ (r + 1))
    (Fin.snoc (α := fun _ : Fin (r + 1) => RD d) u (0 : RD d)) (Fin.last r) a x
  simpa only [← snoc_eq_update] using h

/-- The orthogonal projection onto a submodule is the closest point. -/
lemma norm_sub_starProjection_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Submodule ℝ E) [U.HasOrthogonalProjection] (y : E) {w : E} (hw : w ∈ U) :
    ‖y - U.starProjection y‖ ≤ ‖y - w‖ := by
  have hperp : inner ℝ (y - U.starProjection y) (U.starProjection y - w) = 0 :=
    Submodule.starProjection_inner_eq_zero y _
      (U.sub_mem (Submodule.starProjection_apply_mem U y) hw)
  have hdecomp : y - w = (y - U.starProjection y) + (U.starProjection y - w) := by abel
  have hpyth : ‖y - w‖ ^ 2 = ‖y - U.starProjection y‖ ^ 2 + ‖U.starProjection y - w‖ ^ 2 := by
    have h := (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
      (y - U.starProjection y) (U.starProjection y - w)).mpr hperp
    simp only [hdecomp]
    nlinarith [h]
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  nlinarith [hpyth, sq_nonneg ‖U.starProjection y - w‖]

/-- Projecting a vector onto `span (P ∘ e)` does not increase its distance to `span e`. -/
lemma dist_starProjection_le {d m : ℕ} (P : RD d →ₗ[ℝ] RD d) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (e : Fin m → RD d) (x : RD d) :
    ‖P x - (Submodule.span ℝ (Set.range fun k : Fin m => P (e k))).starProjection (P x)‖ ≤
      ‖x - (Submodule.span ℝ (Set.range e)).starProjection x‖ := by
  classical
  set V : Submodule ℝ (RD d) := Submodule.span ℝ (Set.range e) with hV
  set W : Submodule ℝ (RD d) := Submodule.span ℝ (Set.range fun k : Fin m => P (e k)) with hW
  have hzV : V.starProjection x ∈ V := Submodule.starProjection_apply_mem V x
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ (v := e)).mp (by
    simpa only [hV] using hzV)
  have hPW : P (V.starProjection x) ∈ W := by
    rw [← hc, map_sum]
    refine Submodule.sum_mem _ (fun k _ => ?_)
    rw [map_smul, hW]
    exact Submodule.smul_mem _ (c k) (Submodule.subset_span ⟨k, rfl⟩)
  calc ‖P x - W.starProjection (P x)‖ ≤ ‖P x - P (V.starProjection x)‖ :=
        norm_sub_starProjection_le W (P x) hPW
    _ = ‖P (x - V.starProjection x)‖ := by rw [map_sub]
    _ ≤ ‖x - V.starProjection x‖ := hP _
    _ = ‖x - V.starProjection x‖ := rfl

/-- **One-step orthonormal extension.**  Let `P` be a contraction, `e : Fin m → ℝᵈ` an
orthonormal family contained in a subspace `W` with `‖⋀^m e‖ = 1` and a large `π₊`-wedge, and
`u : Fin i → ℝᵈ` an orthonormal family of `W` with `ε ≤ ‖⋀^i P (u₁∧…∧u_i)‖`, `m < i`.  Then
there is a unit vector `u' ∈ W`, orthogonal to all `e_k`, whose `π₊`-wedge with `e` is at least
`ε γ`. -/
theorem exists_unit_orthogonal_extension {d m i : ℕ} (P : RD d →ₗ[ℝ] RD d)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hmi : m < i) (W : Submodule ℝ (RD d))
    (e : Fin m → RD d) (heW : ∀ k, e k ∈ W) (he1 : ‖exteriorPower.ιMulti ℝ m e‖ = 1)
    (u : Fin i → RD d) (hu : Orthonormal ℝ u) (huW : ∀ k, u k ∈ W)
    {ε γ : ℝ} (hε : 0 < ε) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγε : (2 : ℝ) ^ i * γ ^ (i - m) < ε)
    (hbig : ε ≤ ‖exteriorPower.ιMulti ℝ i (fun k => P (u k))‖)
    (hπ : ε ≤ ‖exteriorPower.ιMulti ℝ m (fun k => P (e k))‖) :
    ∃ u' : RD d, ‖u'‖ = 1 ∧ u' ∈ W ∧ (∀ k, inner ℝ u' (e k) = 0) ∧
      ε * γ ≤ ‖exteriorPower.map (m + 1) P
        (exteriorPower.ιMulti ℝ (m + 1) (Fin.snoc e u'))‖ := by
  classical
  have hπ' : ε * ‖exteriorPower.ιMulti ℝ m e‖ ≤
      ‖exteriorPower.ιMulti ℝ m (fun k : Fin m => P (e k))‖ := by
    rw [he1, mul_one]
    exact hπ
  obtain ⟨k, hkdist, hk⟩ := Lemma5Second.lemma5_second_assertion (d := d) P hP m i hmi e u hu
    hε hγ0 hγ1 hγε hbig hπ'
  set V : Submodule ℝ (RD d) := Submodule.span ℝ (Set.range e) with hV
  have hVW : V ≤ W := Submodule.span_le.mpr (by rintro x ⟨j, rfl⟩; exact heW j)
  have hdist : γ ≤ ‖u k - V.starProjection (u k)‖ :=
    le_trans hkdist (dist_starProjection_le P hP e (u k))
  have hpos : 0 < ‖u k - V.starProjection (u k)‖ := lt_of_lt_of_le hγ0 hdist
  have hzorth : u k - V.starProjection (u k) ∈ Vᗮ :=
    Submodule.sub_starProjection_mem_orthogonal (u k)
  refine ⟨(‖u k - V.starProjection (u k)‖)⁻¹ • (u k - V.starProjection (u k)), ?_, ?_, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, inv_mul_cancel₀ (ne_of_gt hpos)]
  · exact W.smul_mem _ (W.sub_mem (huW k) (hVW (Submodule.starProjection_apply_mem V (u k))))
  · intro j
    rw [inner_smul_left]
    have hj : e j ∈ V := Submodule.subset_span ⟨j, rfl⟩
    have h0 : inner ℝ (u k - V.starProjection (u k)) (e j) = 0 := by
      have := (Submodule.mem_orthogonal' V (u k - V.starProjection (u k))).mp hzorth (e j) hj
      exact this
    rw [h0, mul_zero]
  · -- the cone estimate
    have hzmem : V.starProjection (u k) ∈ Submodule.span ℝ (Set.range e) := by
      simpa [hV] using Submodule.starProjection_apply_mem V (u k)
    have hzero : exteriorPower.ιMulti ℝ (m + 1)
        (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (V.starProjection (u k))) = 0 :=
      iMulti_snoc_eq_zero_of_mem_span e hzmem
    have hsub : exteriorPower.ιMulti ℝ (m + 1)
        (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e
          (u k - V.starProjection (u k))) =
        exteriorPower.ιMulti ℝ (m + 1)
          (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k)) := by
      rw [iMulti_snoc_sub, hzero, sub_zero]
    have hI : exteriorPower.ιMulti ℝ (m + 1)
        (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e
          ((‖u k - V.starProjection (u k)‖)⁻¹ • (u k - V.starProjection (u k)))) =
        (‖u k - V.starProjection (u k)‖)⁻¹ •
          exteriorPower.ιMulti ℝ (m + 1)
            (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k)) := by
      rw [iMulti_snoc_smul, hsub]
    have hkc : ε * γ * ‖exteriorPower.ιMulti ℝ (m + 1)
        (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k))‖ ≤
        ‖exteriorPower.map (m + 1) P
          (exteriorPower.ιMulti ℝ (m + 1)
            (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k)))‖ := by
      rw [exteriorPower.map_apply_ιMulti]
      have hcomp : Fin.snoc (α := fun _ : Fin (m + 1) => RD d)
            (fun j : Fin m => P (e j)) (P (u k)) = P ∘ Fin.snoc e (u k) :=
        snoc_comp (⇑P) e (u k)
      rw [← hcomp]
      exact hk
    have hnorm : ‖exteriorPower.ιMulti ℝ (m + 1)
        (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k))‖ =
        ‖u k - V.starProjection (u k)‖ := by
      rw [norm_iMulti_snoc_eq_mul_dist, he1, one_mul]
    rw [hI, map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    calc ε * γ ≤ (‖u k - V.starProjection (u k)‖)⁻¹ *
          ((‖u k - V.starProjection (u k)‖) * (ε * γ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]
      _ = (‖u k - V.starProjection (u k)‖)⁻¹ *
          (ε * γ * ‖u k - V.starProjection (u k)‖) := by ring
      _ = (‖u k - V.starProjection (u k)‖)⁻¹ *
          (ε * γ * ‖exteriorPower.ιMulti ℝ (m + 1)
            (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k))‖) := by rw [hnorm]
      _ ≤ (‖u k - V.starProjection (u k)‖)⁻¹ *
          ‖exteriorPower.map (m + 1) P
            (exteriorPower.ιMulti ℝ (m + 1)
              (Fin.snoc (α := fun _ : Fin (m + 1) => RD d) e (u k)))‖ :=
          mul_le_mul_of_nonneg_left hkc (inv_nonneg.mpr hpos.le)

/-- `Fin.snoc` of an orthonormal family with a unit vector orthogonal to it is orthonormal. -/
lemma orthonormal_snoc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}
    (e : Fin m → E) (he : Orthonormal ℝ e) (u : E) (hu1 : ‖u‖ = 1)
    (huorth : ∀ k, inner ℝ u (e k) = 0) :
    Orthonormal ℝ (Fin.snoc (α := fun _ : Fin (m + 1) => E) e u) := by
  rw [orthonormal_iff_ite]
  intro i j
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last j with ⟨b, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, (orthonormal_iff_ite.mp he) a b]
    by_cases hab : a = b
    · subst hab; simp
    · have h1 : ¬ ((Fin.castSucc a : Fin (m + 1)) = Fin.castSucc b) := fun h =>
        hab (Fin.castSucc_inj.mp h)
      simp [h1, hab]
  · rw [Fin.snoc_castSucc, Fin.snoc_last, real_inner_comm, huorth a]
    simp [Fin.castSucc_ne_last a]
  · rw [Fin.snoc_last, Fin.snoc_castSucc, huorth b]
    simp [(Fin.castSucc_ne_last b).symm]
  · rw [Fin.snoc_last, inner_self_eq_norm_sq_to_K, hu1]
    norm_num

/-- **Prop 5, direction-layer induction.**  Starting from an orthonormal family `e` of size `m`
with the `π₊`-cone condition, and given an orthonormal family `u` of size `i` in `W` with
`‖⋀^i P (u₁∧…∧u_i)‖ ≥ εseq m`, iterate `exists_unit_orthogonal_extension` to obtain an
orthonormal family `e' : Fin i → ℝᵈ` inside `W`, extending `e`, with the cone condition
`εseq i ≤ ‖⋀^i P (e'₁∧…∧e'_i)‖`.

The sequence `εseq` (the running cone constant) and `γ` (the per-step pigeonhole radius) are
parameters, with `εseq (s+1) = εseq s * γ s` and `2^i (γ s)^{i-s} < εseq s`: as recorded in the
ROADMAP, a *constant* `γ` cannot work, the radius has to shrink like the running constant. -/
theorem exists_orthonormal_cone_family {d m i : ℕ} (P : RD d →ₗ[ℝ] RD d)
    (hP : ∀ x, ‖P x‖ ≤ ‖x‖) (hmi : m ≤ i) (hm0 : 1 ≤ m)
    (W : Submodule ℝ (RD d))
    (e : Fin m → RD d) (he : Orthonormal ℝ e) (heW : ∀ k, e k ∈ W)
    (u : Fin i → RD d) (hu : Orthonormal ℝ u) (huW : ∀ k, u k ∈ W)
    (εseq : ℕ → ℝ) (hεpos : ∀ s, 0 < εseq s) (hεle : ∀ s, εseq s ≤ εseq m)
    (hπ : εseq m ≤ ‖exteriorPower.map m P (exteriorPower.ιMulti ℝ m e)‖)
    (hbig : εseq m ≤ ‖exteriorPower.map i P (exteriorPower.ιMulti ℝ i u)‖)
    (γ : ℕ → ℝ) (hγ0 : ∀ s, 0 < γ s) (hγ1 : ∀ s, γ s ≤ 1)
    (hstep : ∀ s, m ≤ s → s < i →
      (2 : ℝ) ^ i * (γ s) ^ (i - s) < εseq s ∧ εseq (s + 1) = εseq s * γ s) :
    ∃ e' : Fin i → RD d, Orthonormal ℝ e' ∧ (∀ k, e' k ∈ W) ∧
      (∀ k : Fin m, e' (Fin.castLE hmi k) = e k) ∧
      εseq i ≤ ‖exteriorPower.map i P (exteriorPower.ιMulti ℝ i e')‖ := by
  classical
  have key : ∀ s (hs : m ≤ s), s ≤ i → ∃ E : Fin s → RD d, Orthonormal ℝ E ∧ (∀ k, E k ∈ W) ∧
      (∀ k : Fin m, E (Fin.castLE hs k) = e k) ∧
      εseq s ≤ ‖exteriorPower.map s P (exteriorPower.ιMulti ℝ s E)‖ := by
    intro s hs
    refine Nat.le_induction ?base ?step s hs
    · intro _
      exact ⟨e, he, heW, fun k => rfl, hπ⟩
    · intro n hmn ih hni
      have hnlt : n < i := Nat.lt_of_succ_le hni
      obtain ⟨E, hEorth, hEW, hEext, hEcone⟩ := ih (Nat.le_of_lt hnlt)
      have hn1 : 1 ≤ n := le_trans hm0 hmn
      have he1' : ‖exteriorPower.ιMulti ℝ n E‖ = 1 :=
        Commons.Analysis.InnerProductSpace.norm_iMulti_orthonormal E hEorth hn1
      obtain ⟨hstep1, hstep2⟩ := hstep n hmn hnlt
      have hbig' : εseq n ≤ ‖exteriorPower.ιMulti ℝ i (fun k : Fin i => P (u k))‖ := by
        rw [exteriorPower.map_apply_ιMulti] at hbig
        exact le_trans (hεle n) hbig
      have hEcone' : εseq n ≤ ‖exteriorPower.ιMulti ℝ n (fun k : Fin n => P (E k))‖ := by
        rw [exteriorPower.map_apply_ιMulti] at hEcone
        exact hEcone
      obtain ⟨u', hu'1, hu'W, hu'orth, hu'cone⟩ :=
        exists_unit_orthogonal_extension P hP hnlt W E hEW he1' u hu huW
          (hεpos n) (hγ0 n) (hγ1 n) hstep1 hbig' hEcone'
      refine ⟨Fin.snoc E u', orthonormal_snoc E hEorth u' hu'1 hu'orth, ?_, ?_, ?_⟩
      · intro k
        rcases Fin.eq_castSucc_or_eq_last k with ⟨a, rfl⟩ | rfl
        · rw [Fin.snoc_castSucc]; exact hEW a
        · rw [Fin.snoc_last]; exact hu'W
      · intro k
        show Fin.snoc (α := fun _ : Fin (n + 1) => RD d) E u'
          (Fin.castLE (Nat.le_succ_of_le hmn) k) = e k
        have hk : Fin.castLE (Nat.le_succ_of_le hmn) k = (Fin.castLE hmn k).castSucc := rfl
        rw [hk, Fin.snoc_castSucc]
        exact hEext k
      · rw [hstep2]
        exact hu'cone
  exact key i hmi le_rfl

end Submission.Lemma5Extension

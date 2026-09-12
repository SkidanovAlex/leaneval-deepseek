import Mathlib
import Submission.Commons.PeriodicTiling.isContinuousTiling_of_isTiling_lift

namespace Commons.PeriodicTiling

open Filter Bornology MeasureTheory
open scoped Pointwise

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem isContinuousTiling_rigid_of_lift
    {d : ℕ} {R : Set (Fin d → ℝ)}
    (hR : IsContinuousTiling R {x : Fin d → ℝ | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)})
    {F : Set (Fin d → ℤ)} (hFne : F.Nonempty)
    {Λ : Set (Fin d → ℝ)} (hΛcount : Λ.Countable)
    (h : IsContinuousTiling (((fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F) + R) Λ) :
    IsContinuousTiling R (Λ + (fun z : Fin d → ℤ => fun i : Fin d => (z i : ℝ)) '' F) := by
  classical
  let emb : (Fin d → ℤ) → (Fin d → ℝ) := fun z => fun i => (z i : ℝ)
  let Z : Set (Fin d → ℝ) := {x | ∃ z : Fin d → ℤ, ∀ i : Fin d, x i = (z i : ℝ)}
  let E : Set (Fin d → ℝ) := emb '' F
  have hE_count : E.Countable := by
    have hF_count : F.Countable := Set.Countable.mono (Set.subset_univ F) (Set.countable_univ : Set.univ.Countable)
    simpa [E, emb] using hF_count.image emb
  have hS_count : (Λ + E).Countable := by
    simpa [Set.image2_add] using Set.Countable.image2 hΛcount hE_count (fun a b => a + b)
  haveI : Countable (Λ + E) := hS_count.to_subtype
  let P : (Fin d → ℝ) → Prop := fun y => ∃! n ∈ Z, y ∈ n +ᵥ R
  let Q : (Fin d → ℝ) → Prop := fun x => ∃! v ∈ Λ, x ∈ v +ᵥ (E + R)
  have hP : ∀ᵐ x, P x := by
    simpa [IsContinuousTiling, P, Z] using hR
  have hQ : ∀ᵐ x, Q x := by
    simpa [IsContinuousTiling, Q, E, emb] using h
  have hP_shift : ∀ a : Fin d → ℝ, ∀ᵐ x, P (x - a) := by
    intro a
    have hq := MeasureTheory.quasiMeasurePreserving_add_left
      (μ := (volume : Measure (Fin d → ℝ))) (-a)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hq.ae (p := P) hP
  have hPall_subtype : ∀ᵐ x, ∀ w : (Λ + E), P (x - (w : Fin d → ℝ)) := by
    rw [ae_all_iff]
    intro w
    exact hP_shift (w : Fin d → ℝ)
  have hPall : ∀ᵐ x, ∀ w ∈ (Λ + E), P (x - w) := by
    exact hPall_subtype.mono fun x hx w hw => hx ⟨w, hw⟩
  have hgood : ∀ᵐ x, Q x ∧ ∀ w ∈ (Λ + E), P (x - w) := hQ.and hPall
  refine hgood.mono ?_
  intro x hx
  rcases hx with ⟨hxQ, hxP⟩
  rcases hxQ with ⟨lam, hlam, hlamuniq⟩
  rcases hlam with ⟨hlamΛ, hxlam⟩
  rcases Set.mem_vadd_set.mp hxlam with ⟨y, hyER, hxy⟩
  rcases Set.mem_add.mp hyER with ⟨e, heE, r, hrR, her⟩
  have hx_eq : x = lam + e + r := by
    calc
      x = lam +ᵥ y := hxy.symm
      _ = lam + y := by rw [vadd_eq_add]
      _ = lam + (e + r) := by rw [← her]
      _ = lam + e + r := by abel
  have hw_mem : lam + e ∈ Λ + E := Set.add_mem_add hlamΛ heE
  have hx_mem : x ∈ (lam + e) +ᵥ R := by
    refine Set.mem_vadd_set.mpr ⟨r, hrR, ?_⟩
    simpa [vadd_eq_add] using hx_eq.symm
  refine ⟨lam + e, ?_, ?_⟩
  · exact ⟨by simpa [E, emb] using hw_mem, hx_mem⟩
  · intro w hw
    rcases hw with ⟨hwmem, hxw⟩
    have hwE : w ∈ Λ + E := by simpa [E, emb] using hwmem
    rcases Set.mem_add.mp hwE with ⟨lam', hlam'Λ, e', he'E, hw_eq⟩
    have hx_mem' : x ∈ lam' +ᵥ (E + R) := by
      rcases Set.mem_vadd_set.mp hxw with ⟨r', hr'R, hxwr⟩
      refine Set.mem_vadd_set.mpr ⟨e' + r', Set.add_mem_add he'E hr'R, ?_⟩
      have h1 : lam' + (e' + r') = x := by
        calc
          lam' + (e' + r') = (lam' + e') + r' := by abel
          _ = w + r' := by rw [hw_eq]
          _ = x := by simpa [vadd_eq_add] using hxwr
      simpa [vadd_eq_add] using h1
    have hll' : lam' = lam := hlamuniq lam' ⟨hlam'Λ, hx_mem'⟩
    have hw_sub : w = lam + e' := by
      calc
        w = lam' + e' := hw_eq.symm
        _ = lam + e' := by rw [hll']
    have hxw_lam : x ∈ (lam + e') +ᵥ R := by
      simpa [hw_sub] using hxw
    rcases Set.mem_vadd_set.mp hx_mem with ⟨r, hrR, hxr⟩
    rcases Set.mem_vadd_set.mp hxw_lam with ⟨r', hr'R, hxr'⟩
    have hxr_add : lam + e + r = x := by
      simpa [vadd_eq_add] using hxr
    have hxr'_add : lam + e' + r' = x := by
      simpa [vadd_eq_add] using hxr'
    have hy0 : x - lam - e = r := by
      rw [← hxr_add]
      abel
    have hy0' : x - lam - e' = r' := by
      rw [← hxr'_add]
      abel
    have hP0 : P (x - lam - e) := by
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxP (lam + e) hw_mem
    rcases hP0 with ⟨n, hn, hnuniq⟩
    rcases hn with ⟨hnZ, hyn⟩
    have hZ0 : (0 : Fin d → ℝ) ∈ Z := by
      refine ⟨0, ?_⟩
      intro i
      simp
    have hZe : e' - e ∈ Z := by
      rcases heE with ⟨ze, hze, rfl⟩
      rcases he'E with ⟨ze', hze', rfl⟩
      refine ⟨ze' - ze, ?_⟩
      intro i
      simp [emb, Pi.sub_apply, Int.cast_sub]
    have hy_in_0 : (x - lam - e) ∈ (0 : Fin d → ℝ) +ᵥ R := by
      refine Set.mem_vadd_set.mpr ⟨r, hrR, ?_⟩
      rw [zero_vadd]
      exact hy0.symm
    have hy_in_diff : (x - lam - e) ∈ (e' - e) +ᵥ R := by
      refine Set.mem_vadd_set.mpr ⟨r', hr'R, ?_⟩
      rw [vadd_eq_add]
      rw [← hy0']
      abel
    have h0eq : (0 : Fin d → ℝ) = n := hnuniq (0 : Fin d → ℝ) ⟨hZ0, hy_in_0⟩
    have hdeq : e' - e = n := hnuniq (e' - e) ⟨hZe, hy_in_diff⟩
    have hee : e' - e = 0 := hdeq.trans h0eq.symm
    have hee' : e' = e := sub_eq_zero.mp hee
    calc
      w = lam' + e' := hw_eq.symm
      _ = lam + e' := by rw [hll']
      _ = lam + e := by rw [hee']

end Commons.PeriodicTiling

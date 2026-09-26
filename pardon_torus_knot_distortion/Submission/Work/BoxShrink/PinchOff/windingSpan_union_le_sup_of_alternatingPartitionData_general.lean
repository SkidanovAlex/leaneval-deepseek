import Mathlib
import Submission.Work.BoxShrink.PinchOff.PairingData
import Submission.Work.BoxShrink.PinchOff.windingSpan_union_le_sup_of_alternatingPartitionData

/-!
# Subadditivity of the winding span over an alternating partition, without vanishing hypotheses

`Work.BoxShrink.PinchOff.windingSpan_union_le_sup_of_alternatingPartitionData_general`: if two
subsets `A`, `B` of the carrier of a parametrised torus carry an
`AlternatingPartitionData` (`PairingData.lean`) — every closed curve of `A ∪ B` is entirely in `A`,
entirely in `B`, or splits into finitely many monochromatic arcs alternating between `A` and `B`
whose `A`-arcs close up inside `A ∩ B` — then

  `WindingSpan P (A ∪ B) ≤ WindingSpan P A ⊔ WindingSpan P B`.

This is the sibling `windingSpan_union_le_sup_of_alternatingPartitionData` with the two
hypotheses `WindingSpan P A = ⊥` and `WindingSpan P B = ⊥` dropped.

The argument is the same as in the vanishing case: a loop `γ` of `A ∪ B` which is not
monochromatic is split at its crossings with the interface into `A`-arcs `a_j` and `B`-arcs
`bb_j`, and the datum supplies connectors `e_j` inside `A ∩ B` with the endpoints of `a_j`.  Then

* each `a_j · e_j⁻¹` is a loop of `A`, and the chain `e_0 · bb_0 · e_1 · bb_1 · ⋯` is a loop of
  `B` — so their winding vectors lie in `WindingSpan P A`, resp. `WindingSpan P B`;
* the `ψ`-displacements of the links telescope: the total displacement of `γ` is the sum of the
  displacements of the `B`-links, whose `A`-corrections are exactly the displacements of the
  `A`-loops — so `windingOf γ` is a sum of winding vectors of an `A`-loop and of a `B`-loop.

The last step is expressed through an auxiliary linear functional `ψ` whose kernel on integer
vectors is exactly the target subspace `V = WindingSpan P A ⊔ WindingSpan P B`
(`winding_mem_of_alternatingPartitionData`).  Since `ℚ × ℚ` is two dimensional, `V` is either
everything, zero, or a line, and in each case such a functional exists.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.BoxShrink.PinchOff

noncomputable section

open scoped unitInterval
open Work.PinchLemma3.ClosedDiscA

set_option linter.unusedVariables false

/-- **The engine.**  If `ψ` is a linear functional whose kernel on integer vectors is exactly the
subspace `V ⊇ WindingSpan P A, WindingSpan P B`, then the winding vector of any closed curve
carrying an alternating partition with connectors in `A ∩ B` lies in `V`. -/
theorem winding_mem_of_alternatingPartitionData
    {P : Work.CoreTopology.ParamTorus} {A B : Set R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    {V : Submodule ℚ (ℚ × ℚ)} {W : Type*} [AddCommGroup W] [Module ℝ W]
    (ψ : (ℝ × ℝ) →ₗ[ℝ] W)
    (hψ : ∀ v : ℤ × ℤ, ((v.1 : ℚ), (v.2 : ℚ)) ∈ V → ψ ((v.1 : ℝ), (v.2 : ℝ)) = 0)
    (hψ' : ∀ v : ℤ × ℤ, ψ ((v.1 : ℝ), (v.2 : ℝ)) = 0 → ((v.1 : ℚ), (v.2 : ℚ)) ∈ V)
    (hVA : Work.SurgeryInvariance.WindingSpan P A ≤ V)
    (hVB : Work.SurgeryInvariance.WindingSpan P B ≤ V)
    (γ : Work.CoreTopology.ClosedCurve P)
    {k : ℕ} (hk : 0 < k) {s : ℕ → ℝ}
    (hs0 : s 0 ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hslast : s (2 * k) = s 0 + 2 * Real.pi)
    (hmono : ∀ i j : ℕ, i ≤ 2 * k → j ≤ 2 * k → i < j → s i < s j)
    (hArcA : ∀ j : ℕ, j < k → ∀ t : ℝ, s (2 * j) ≤ t → t ≤ s (2 * j + 1) → γ t ∈ A)
    (hArcB : ∀ j : ℕ, j < k → ∀ t : ℝ, s (2 * j + 1) ≤ t → t ≤ s (2 * j + 2) → γ t ∈ B)
    (hJoined : ∀ j : ℕ, j < k → JoinedIn (A ∩ B) (γ (s (2 * j))) (γ (s (2 * j + 1)))) :
    (((Work.SurgeryInvariance.windingOf P γ).1 : ℚ),
      ((Work.SurgeryInvariance.windingOf P γ).2 : ℚ)) ∈ V := by
  classical
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  set Λ : ℝ → ℝ × ℝ := fun t => (L.Θ t, L.Φ t) with hΛdef
  have hΛc : Continuous Λ := L.contΘ.prodMk L.contΦ
  have hΛmem : ∀ t : ℝ, Work.TorusCover.psiMap P.psi (Λ t) = γ t := by
    intro t; simp only [hΛdef, Work.TorusCover.psiMap]; exact L.lifts t
  let b : ℕ → P.carrier := fun i => ⟨γ (s i), γ.mem (s i)⟩
  have hs01 : s 0 ≤ s 1 := le_of_lt (hmono 0 1 (by omega) (by omega) (by omega))
  have hA_even : ∀ j : ℕ, j ≤ k → γ (s (2 * j)) ∈ A := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj' | hj'
    · exact hArcA j hj' (s (2 * j)) (le_refl _)
        (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega)))
    · rw [hj', hslast, γ.periodic (s 0)]
      exact hArcA 0 hk (s 0) (le_refl _) hs01
  have hB_even : ∀ j : ℕ, j ≤ k → γ (s (2 * j)) ∈ B := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj' | hj'
    · rw [hj', ← γ.periodic (s 0), ← hslast]
      exact hArcB (k - 1) (by omega) (s (2 * k))
        (le_of_lt (hmono (2 * (k - 1) + 1) (2 * k) (by omega) (by omega) (by omega)))
        (le_of_eq (by congr 1; omega))
    · exact hArcB (j - 1) (by omega) (s (2 * j))
        (le_of_lt (hmono (2 * (j - 1) + 1) (2 * j) (by omega) (by omega) (by omega)))
        (le_of_eq (by congr 1; omega))
  have hA_odd : ∀ j : ℕ, j < k → γ (s (2 * j + 1)) ∈ A := fun j hj =>
    hArcA j hj (s (2 * j + 1))
      (le_of_lt (hmono (2 * j) (2 * j + 1) (by omega) (by omega) (by omega))) (le_refl _)
  have hB_odd : ∀ j : ℕ, j < k → γ (s (2 * j + 1)) ∈ B := fun j hj =>
    hArcB j hj (s (2 * j + 1)) (le_refl _)
      (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))
  let a : (j : Fin k) → Path (b (2 * j.val)) (b (2 * j.val + 1)) :=
    fun j => subArc γ (s (2 * j.val)) (s (2 * j.val + 1))
  have ha_mem : ∀ (j : Fin k) (t : unitInterval), ((a j) t : R3) ∈ A := by
    intro j t
    exact subArc_coe_mem γ
      (le_of_lt (hmono (2 * j.val) (2 * j.val + 1) (by have := j.isLt; omega)
        (by have := j.isLt; omega) (by have := j.isLt; omega)))
      (fun u hu1 hu2 => hArcA j.val j.isLt u hu1 hu2) t
  -- the connectors inside `A ∩ B`, supplied by the datum
  have hconn : ∀ j : Fin k, ∃ c : Path (b (2 * j.val)) (b (2 * j.val + 1)),
      ∀ t : unitInterval, (c t : R3) ∈ A ∩ B := by
    intro j
    obtain ⟨c, hc⟩ := hJoined j.val j.isLt
    refine ⟨⟨⟨fun t => ⟨c t, hAc (hc t).1⟩, c.continuous.subtype_mk _⟩, ?_, ?_⟩,
      fun t => ⟨(hc t).1, (hc t).2⟩⟩
    · exact Subtype.ext c.source
    · exact Subtype.ext c.target
  let e : (j : Fin k) → Path (b (2 * j.val)) (b (2 * j.val + 1)) :=
    fun j => Classical.choose (hconn j)
  have he : ∀ (j : Fin k) (t : unitInterval), (e j t : R3) ∈ A ∩ B :=
    fun j => Classical.choose_spec (hconn j)
  -- each `A`-arc closes up through `A ∩ B` into a loop of `A`, which is `ψ`-null
  have hAloop : ∀ j : Fin k, psiDisp ψ ((a j).trans ((e j).symm)) = 0 := by
    intro j
    exact psiDisp_eq_zero_of_subset ψ hψ hVA ((a j).trans ((e j).symm)) (fun t =>
      Path.trans_coe_mem (a j) ((e j).symm) (fun u => ha_mem j u)
        (Path.symm_coe_mem (e j) (fun u => (he j u).1)) t)
  have hDa : ∀ j : Fin k, psiDisp ψ (a j) = psiDisp ψ (e j) := by
    intro j
    have h := hAloop j
    rw [psiDisp_trans, psiDisp_symm] at h
    have h'' : psiDisp ψ (a j) - psiDisp ψ (e j) = 0 := by
      simpa [sub_eq_add_neg] using h
    exact sub_eq_zero.mp h''
  -- the chain of `B`-pieces: `e_j` followed by the `B`-arc from `s (2j+1)` to `s (2j+2)`
  let bb : ∀ j, j < k → Path (b (2 * j + 1)) (b (2 * j + 2)) := fun j _ =>
    subArc γ (s (2 * j + 1)) (s (2 * j + 2))
  have hbb_mem : ∀ (j : ℕ) (hj : j < k) (t : unitInterval), ((bb j hj) t : R3) ∈ B := by
    intro j hj t
    exact subArc_coe_mem γ
      (le_of_lt (hmono (2 * j + 1) (2 * j + 2) (by omega) (by omega) (by omega)))
      (fun u hu1 hu2 => hArcB j hj u hu1 hu2) t
  let c : ℕ → P.carrier := fun j => b (2 * j)
  let w : ∀ j, j < k → Path (c j) (c (j + 1)) := fun j hj => (e ⟨j, hj⟩).trans (bb j hj)
  have hw_mem : ∀ j (hj : j < k) (t : unitInterval), ((w j hj) t : R3) ∈ B := by
    intro j hj t
    exact Path.trans_coe_mem (Y := B) (e ⟨j, hj⟩) (bb j hj) (fun u => (he ⟨j, hj⟩ u).2)
      (fun u => hbb_mem j hj u) t
  have hck : c k = b 0 := Subtype.ext (by
    show γ (s (2 * k)) = γ (s 0)
    rw [hslast]; exact γ.periodic (s 0))
  have hchain_mem : ∀ t : unitInterval, ((chainPath k w) t : R3) ∈ B := by
    refine chainPath_mem (X := B) ?_ k w hw_mem
    exact hB_even 0 (by omega)
  -- the chain closes up into a loop of `B`, which is `ψ`-null
  have hchain_psi : psiDisp ψ (chainPath k w) = 0 := by
    let loop : Path (b 0) (b 0) :=
      ⟨(chainPath k w).toContinuousMap, (chainPath k w).source,
        (chainPath k w).target.trans hck⟩
    have hloop_mem : ∀ t : unitInterval, (loop t : R3) ∈ B := fun t => hchain_mem t
    have h0 : psiDisp ψ loop = 0 := psiDisp_eq_zero_of_subset ψ hψ hVB loop hloop_mem
    exact (show psiDisp ψ loop = psiDisp ψ (chainPath k w) from rfl) ▸ h0
  have hsum : ∑ j : Fin k, psiDisp ψ (w j.val j.isLt) = 0 := by
    rw [← psiDisp_chainPath ψ k w]
    exact hchain_psi
  -- the displacement of the `j`-th link
  have hsummand : ∀ j : Fin k, psiDisp ψ (w j.val j.isLt) =
      ψ (Λ (s (2 * j.val + 2))) - ψ (Λ (s (2 * j.val))) := by
    intro j
    have hj := j.isLt
    show psiDisp ψ ((e ⟨j.val, hj⟩).trans (bb j.val hj)) =
      ψ (Λ (s (2 * j.val + 2))) - ψ (Λ (s (2 * j.val)))
    rw [psiDisp_trans, ← hDa ⟨j.val, hj⟩,
      psiDisp_subArc ψ γ (s (2 * j.val)) (s (2 * j.val + 1)) Λ hΛc hΛmem,
      psiDisp_subArc ψ γ (s (2 * j.val + 1)) (s (2 * j.val + 2)) Λ hΛc hΛmem]
    abel
  -- telescoping over the even parameters
  have htel : ∑ j : Fin k, (ψ (Λ (s (2 * j.val + 2))) - ψ (Λ (s (2 * j.val)))) =
      ψ (Λ (s (2 * k))) - ψ (Λ (s 0)) := by
    have hsum1 : (∑ j : Fin k, (ψ (Λ (s (2 * j.val + 2))) - ψ (Λ (s (2 * j.val)))))
        = ∑ j ∈ Finset.range k, (ψ (Λ (s (2 * (j + 1)))) - ψ (Λ (s (2 * j)))) := by
      rw [Fin.sum_univ_eq_sum_range (fun j => ψ (Λ (s (2 * j + 2))) - ψ (Λ (s (2 * j)))) k]
      exact Finset.sum_congr rfl (fun j _ => by rw [Nat.mul_succ])
    rw [hsum1, Finset.sum_range_sub (fun j => ψ (Λ (s (2 * j))))]
  have hzero : ψ (Λ (s (2 * k))) - ψ (Λ (s 0)) = 0 := by
    rw [← htel]
    exact (Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hsummand j)).symm.trans hsum
  have hper : Λ (s (2 * k)) =
      Λ (s 0) + Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ) := by
    have h := L.period_shift_winding (s 0)
    have hw := Work.SurgeryInvariance.windingOf_eq P γ L
    rw [hslast, hw]
    ext <;> simp [hΛdef, Work.TorusCover.periodShift, h.1, h.2]
  have hpsi0 : ψ (((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
      ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) = 0 := by
    have h2 : ψ (Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ)) = 0 := by
      have hh := hzero
      rw [hper, map_add, sub_eq_add_neg] at hh
      rw [show ψ (Λ (s 0)) + ψ (Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ))
          + -ψ (Λ (s 0)) = ψ (Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ))
          from by abel] at hh
      exact hh
    rw [show Work.TorusCover.periodShift (Work.SurgeryInvariance.windingOf P γ)
        = (2 * Real.pi) • ((((Work.SurgeryInvariance.windingOf P γ).1 : ℝ),
            ((Work.SurgeryInvariance.windingOf P γ).2 : ℝ)) : ℝ × ℝ) from by
          ext <;> simp [Work.TorusCover.periodShift, smul_eq_mul, mul_comm],
      map_smul] at h2
    exact (smul_eq_zero.mp h2).resolve_left (by positivity)
  exact hψ' _ hpsi0

/-- **Subadditivity of the winding span over an alternating partition.** -/
theorem windingSpan_union_le_sup_of_alternatingPartitionData_general
    {P : Work.CoreTopology.ParamTorus} {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (h : Work.BoxShrink.PinchOff.AlternatingPartitionData P A B) :
    Work.SurgeryInvariance.WindingSpan P (A ∪ B) ≤
      Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B := by
  by_cases htop : Work.SurgeryInvariance.WindingSpan P A ⊔
      Work.SurgeryInvariance.WindingSpan P B = ⊤
  · rw [htop]; exact le_top
  · by_cases hbot : Work.SurgeryInvariance.WindingSpan P A ⊔
        Work.SurgeryInvariance.WindingSpan P B = ⊥
    · have hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥ :=
        le_bot_iff.mp (hbot ▸ le_sup_left)
      have hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥ :=
        le_bot_iff.mp (hbot ▸ le_sup_right)
      rw [hbot]
      exact hbot ▸ windingSpan_union_le_sup_of_alternatingPartitionData hAc hBc h hVA hVB
    · rcases exists_functional_kernel_eq
          (Work.SurgeryInvariance.WindingSpan P A ⊔ Work.SurgeryInvariance.WindingSpan P B)
          hbot htop with ⟨a', b', hab, hker⟩
      let ψ : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
        { toFun := fun p => (b' : ℝ) * p.1 - (a' : ℝ) * p.2
          map_add' := by intro p q; simp only [Prod.fst_add, Prod.snd_add]; ring
          map_smul' := by
            intro c p
            simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]; ring }
      have hψ : ∀ w : ℤ × ℤ,
          (((w.1 : ℚ), (w.2 : ℚ)) ∈
            (Work.SurgeryInvariance.WindingSpan P A ⊔
              Work.SurgeryInvariance.WindingSpan P B)) →
          ψ ((w.1 : ℝ), (w.2 : ℝ)) = 0 := by
        intro w hw
        have h := (hker w).mp hw
        show (b' : ℝ) * (w.1 : ℝ) - (a' : ℝ) * (w.2 : ℝ) = 0
        exact_mod_cast h
      have hψ' : ∀ w : ℤ × ℤ, ψ ((w.1 : ℝ), (w.2 : ℝ)) = 0 →
          (((w.1 : ℚ), (w.2 : ℚ)) ∈
            (Work.SurgeryInvariance.WindingSpan P A ⊔
              Work.SurgeryInvariance.WindingSpan P B)) := by
        intro w hw
        refine (hker w).mpr ?_
        have h : (b' : ℝ) * (w.1 : ℝ) - (a' : ℝ) * (w.2 : ℝ) = 0 := hw
        exact_mod_cast h
      rw [Work.SurgeryInvariance.WindingSpan, Submodule.span_le]
      rintro v ⟨γ, hγ, rfl⟩
      rcases h γ hγ with hγA | hγB | ⟨k, hk, s, hs0, hslast, hmono, hArcA, hArcB, hJoined⟩
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨γ, hγA, rfl⟩)
      · exact Submodule.mem_sup_right (Submodule.subset_span ⟨γ, hγB, rfl⟩)
      · exact winding_mem_of_alternatingPartitionData hAc hBc ψ hψ hψ'
          le_sup_left le_sup_right γ hk hs0 hslast hmono hArcA hArcB hJoined

end

end Work.BoxShrink.PinchOff

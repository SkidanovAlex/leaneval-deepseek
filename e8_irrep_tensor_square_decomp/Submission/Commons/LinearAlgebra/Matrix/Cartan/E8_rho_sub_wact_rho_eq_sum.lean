import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posRoots_finset
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_coords_same_sign

open scoped BigOperators

namespace Commons.LinearAlgebra.Matrix.Cartan

lemma alpha_eq_E8posRoots (i : Fin 8) : E8posRoots.alpha i = alpha i := by
  funext j; rw [alpha_apply]; rfl

lemma qz_sref' (i : Fin 8) (v : Fin 8 → ℤ) : E8NormTwo.qZ (sref i v) = E8NormTwo.qZ v :=
  E8posRoots.qz_sref i v

lemma qz_wact' (L : List (Fin 8)) (v : Fin 8 → ℤ) : E8NormTwo.qZ (wact L v) = E8NormTwo.qZ v :=
  E8posRoots.qz_wact L v

noncomputable def E8negP : Finset (Fin 8 → ℤ) := E8posRoots.P.image (fun v => -v)

lemma mem_E8negP (v : Fin 8 → ℤ) : v ∈ E8negP ↔ -v ∈ E8posRoots.P := by
  unfold E8negP
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, huv⟩
    rw [← huv]; simpa using hu
  · intro h; exact ⟨-v, h, by simp⟩

lemma neg_mem_E8negP (v : Fin 8 → ℤ) : -v ∈ E8negP ↔ v ∈ E8posRoots.P := by
  rw [mem_E8negP]; simp

lemma not_mem_E8negP_of_memP (v : Fin 8 → ℤ) (hv : v ∈ E8posRoots.P) : v ∉ E8negP := by
  intro hneg
  rw [mem_E8negP] at hneg
  obtain ⟨hq, hne, hc⟩ := (E8posRoots.memP v).mp hv
  obtain ⟨hq2, hne2, hc2⟩ := (E8posRoots.memP (-v)).mp hneg
  have hc0 : ∀ j, E8posRoots.coords v j = 0 := by
    intro j
    have h1 : 0 ≤ E8posRoots.coords v j := hc j
    have h2 : 0 ≤ E8posRoots.coords (-v) j := hc2 j
    have h3 : E8posRoots.coords (-v) j = - E8posRoots.coords v j := by
      rw [E8posRoots.coords_neg]; rfl
    omega
  have hq0 : E8NormTwo.qZ v = 0 := by
    rw [E8posRoots.qz_eq_dot]
    exact Finset.sum_eq_zero (fun j _ => by rw [hc0 j, zero_mul])
  omega

lemma not_memP_of_mem_E8negP (v : Fin 8 → ℤ) (hv : v ∈ E8negP) : v ∉ E8posRoots.P :=
  fun hP => not_mem_E8negP_of_memP v hP hv

lemma sref_neg (i : Fin 8) (v : Fin 8 → ℤ) : sref i (-v) = - sref i v := by
  funext j
  simp only [sref_apply, Pi.neg_apply]
  ring

lemma wact_neg (L : List (Fin 8)) (v : Fin 8 → ℤ) : wact L (-v) = - wact L v := by
  induction L generalizing v with
  | nil => rfl
  | cons i L ih =>
      rw [wact_cons, wact_cons, sref_neg, ih]

lemma sref_neg_alpha (i : Fin 8) : sref i (- alpha i) = alpha i := by
  rw [sref_neg, sref_alpha_self, neg_neg]

lemma sref_posRoot (i : Fin 8) (v : Fin 8 → ℤ) (hv : v ∈ E8posRoots.P) (hne : v ≠ alpha i) :
    sref i v ∈ E8posRoots.P := by
  rw [E8posRoots.memP]
  exact E8posRoots.sref_mem_posRoot i v ((E8posRoots.memP v).mp hv)
    (fun h => hne (by rw [← alpha_eq_E8posRoots i]; exact h))

lemma alpha_memP (i : Fin 8) : alpha i ∈ E8posRoots.P := by
  rw [E8posRoots.memP]
  refine ⟨?_, alpha_ne_zero i, fun j => ?_⟩
  · rw [qZ_eq_bil, bil_apply, E8m_diag]
  · have hca : E8posRoots.coords (alpha i) = Pi.single i 1 := coords_alpha i
    rw [hca]
    by_cases h : j = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

lemma root_mem_P_or_negP (v : Fin 8 → ℤ) (hq : E8NormTwo.qZ v = 2) (hne : v ≠ 0) :
    v ∈ E8posRoots.P ∨ v ∈ E8negP := by
  have hq' : (∑ i, ∑ j, v i * E8NormTwo.E8inv i j * v j) = 2 := by
    rw [← E8posRoots.qz_eq_sum]; exact hq
  rcases E8_coords_same_sign v hne hq' with h | h
  · left
    refine (E8posRoots.memP v).mpr ⟨hq, hne, fun i => ?_⟩
    rw [E8posRoots.coords_apply]; exact h i
  · right
    rw [mem_E8negP]
    refine (E8posRoots.memP (-v)).mpr ⟨?_, ?_, fun i => ?_⟩
    · rw [E8_qZ_neg]; exact hq
    · intro h0; exact hne (neg_eq_zero.mp h0)
    · rw [E8posRoots.coords_apply]
      have h1 : E8posRoots.coords (-v) i = - E8posRoots.coords v i := by
        rw [E8posRoots.coords_neg]; rfl
      rw [← E8posRoots.coords_apply, h1, E8posRoots.coords_apply]
      exact neg_nonneg.mpr (h i)

lemma sref_mem_P_or_negP (i : Fin 8) (v : Fin 8 → ℤ) (hv : v ∈ E8posRoots.P) :
    sref i v ∈ E8posRoots.P ∨ sref i v ∈ E8negP := by
  have hq := (E8posRoots.memP v).mp hv
  have hqz : E8NormTwo.qZ (sref i v) = 2 := by
    rw [qz_sref']; exact hq.1
  have hne : sref i v ≠ 0 := by
    intro h0
    have h1 : sref i (sref i v) = sref i 0 := by rw [h0]
    rw [sref_invol, sref_zero] at h1
    exact hq.2.1 h1
  exact root_mem_P_or_negP (sref i v) hqz hne

lemma sref_mem_negP_iff (i : Fin 8) (v : Fin 8 → ℤ) (hv : v ∈ E8posRoots.P) :
    sref i v ∈ E8negP ↔ v = alpha i := by
  constructor
  · intro hneg
    by_contra hne
    have hP : sref i v ∈ E8posRoots.P := sref_posRoot i v hv hne
    exact not_mem_E8negP_of_memP (sref i v) hP hneg
  · intro hv_eq
    rw [mem_E8negP, hv_eq, sref_alpha_self]
    simp only [neg_neg]
    exact alpha_memP i

lemma sref_memP_iff (i : Fin 8) (v : Fin 8 → ℤ) (hv : v ∈ E8posRoots.P) :
    sref i v ∈ E8posRoots.P ↔ v ≠ alpha i := by
  have hdisj := sref_mem_P_or_negP i v hv
  have hneg := sref_mem_negP_iff i v hv
  constructor
  · intro hP hveq
    exact not_mem_E8negP_of_memP (sref i v) hP (hneg.mpr hveq)
  · intro hne
    rcases hdisj with h | h
    · exact h
    · exact absurd (hneg.mp h) hne

lemma sref_mem_negP_iff_of_mem_negP (i : Fin 8) (v : Fin 8 → ℤ) (hv : v ∈ E8negP) :
    sref i v ∈ E8negP ↔ v ≠ - alpha i := by
  have hvP : -v ∈ E8posRoots.P := (mem_E8negP v).mp hv
  have hsref : sref i v = - sref i (-v) := by rw [sref_neg]; simp
  have hstep : sref i v ∈ E8negP ↔ sref i (-v) ∈ E8posRoots.P := by
    rw [mem_E8negP, hsref]
    simp
  rw [hstep, sref_memP_iff i (-v) hvP]
  constructor
  · intro h hveq
    exact h (by rw [hveq]; simp)
  · intro h hnegv
    exact h (by rw [← hnegv]; simp)

lemma wact_mem_P_or_negP (L : List (Fin 8)) (v : Fin 8 → ℤ) (hv : v ∈ E8posRoots.P) :
    wact L v ∈ E8posRoots.P ∨ wact L v ∈ E8negP := by
  have hq := (E8posRoots.memP v).mp hv
  have hqz : E8NormTwo.qZ (wact L v) = 2 := by
    rw [qz_wact']; exact hq.1
  have hne : wact L v ≠ 0 := by
    intro h0
    have h1 : wact L.reverse (wact L v) = wact L.reverse 0 := by rw [h0]
    rw [wact_reverse, wact_zero] at h1
    exact hq.2.1 h1
  exact root_mem_P_or_negP (wact L v) hqz hne

lemma rho_step (i : Fin 8) (L : List (Fin 8)) :
    (∑ y ∈ E8posRoots.P.filter (fun y => -(wact (i :: L).reverse y) ∈ E8posRoots.P), y)
      = (∑ y ∈ E8posRoots.P.filter (fun y => -(wact L.reverse y) ∈ E8posRoots.P), y)
        + wact L (alpha i) := by
  classical
  have hrev : ∀ y : Fin 8 → ℤ, wact (i :: L).reverse y = sref i (wact L.reverse y) := by
    intro y
    rw [List.reverse_cons, wact_append, wact_singleton]
  have hF1 : E8posRoots.P.filter (fun y => -(wact (i :: L).reverse y) ∈ E8posRoots.P)
      = E8posRoots.P.filter (fun y => sref i (wact L.reverse y) ∈ E8negP) := by
    apply Finset.filter_congr
    intro y _
    rw [hrev y]
    exact (mem_E8negP _).symm
  have hF2 : E8posRoots.P.filter (fun y => -(wact L.reverse y) ∈ E8posRoots.P)
      = E8posRoots.P.filter (fun y => wact L.reverse y ∈ E8negP) := by
    apply Finset.filter_congr
    intro y _
    exact (mem_E8negP _).symm
  rw [hF1, hF2]
  have halP : alpha i ∈ E8posRoots.P := alpha_memP i
  have hgP := wact_mem_P_or_negP L (alpha i) halP
  have hgh : ∀ v : Fin 8 → ℤ, wact L (wact L.reverse v) = v := by
    intro v
    simpa using wact_reverse L.reverse v
  have hhg : ∀ v : Fin 8 → ℤ, wact L.reverse (wact L v) = v := fun v => wact_reverse L v
  have hhroot : ∀ y : Fin 8 → ℤ, y ∈ E8posRoots.P →
      wact L.reverse y ∈ E8posRoots.P ∨ wact L.reverse y ∈ E8negP :=
    fun y hy => wact_mem_P_or_negP L.reverse y hy
  have hkey : ∀ y : Fin 8 → ℤ, wact L.reverse y = - alpha i → y = - wact L (alpha i) := by
    intro y hy
    have h1 := congrArg (wact L) hy
    rw [wact_neg, hgh] at h1
    exact h1
  have hkey2 : ∀ y : Fin 8 → ℤ, wact L.reverse y = alpha i → y = wact L (alpha i) := by
    intro y hy
    have h1 := congrArg (wact L) hy
    rw [hgh] at h1
    exact h1
  have hrevneg : wact L.reverse (- wact L (alpha i)) = - alpha i := by
    rw [wact_neg, hhg]
  rcases hgP with hgP | hgN
  · -- case 1
    have hnotmem : wact L (alpha i) ∉ E8posRoots.P.filter (fun y => wact L.reverse y ∈ E8negP) := by
      intro h
      rw [Finset.mem_filter] at h
      obtain ⟨-, hh⟩ := h
      rw [hhg] at hh
      exact not_mem_E8negP_of_memP (alpha i) halP hh
    have hset : E8posRoots.P.filter (fun y => sref i (wact L.reverse y) ∈ E8negP)
        = insert (wact L (alpha i))
            (E8posRoots.P.filter (fun y => wact L.reverse y ∈ E8negP)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hyP, hcond⟩
        rcases hhroot y hyP with hypos | hyneg
        · left
          exact hkey2 y ((sref_mem_negP_iff i (wact L.reverse y) hypos).mp hcond)
        · right
          exact ⟨hyP, hyneg⟩
      · rintro (hyeq | ⟨hyP, hyneg⟩)
        · subst hyeq
          refine ⟨hgP, ?_⟩
          rw [hhg]
          exact (sref_mem_negP_iff i (alpha i) halP).mpr rfl
        · refine ⟨hyP, ?_⟩
          have hne : wact L.reverse y ≠ - alpha i := by
            intro hcon
            have h1 := hkey y hcon
            have hneg' : - wact L (alpha i) ∈ E8negP := (neg_mem_E8negP _).mpr hgP
            rw [h1] at hyP
            exact not_mem_E8negP_of_memP (- wact L (alpha i)) hyP hneg'
          exact (sref_mem_negP_iff_of_mem_negP i (wact L.reverse y) hyneg).mpr hne
    rw [hset, Finset.sum_insert hnotmem]
    abel
  · -- case 2
    have hzP : - wact L (alpha i) ∈ E8posRoots.P := (mem_E8negP (wact L (alpha i))).mp hgN
    have hzF2 : - wact L (alpha i)
        ∈ E8posRoots.P.filter (fun y => wact L.reverse y ∈ E8negP) := by
      rw [Finset.mem_filter]
      refine ⟨hzP, ?_⟩
      rw [hrevneg]
      exact (neg_mem_E8negP (alpha i)).mpr halP
    have hset : E8posRoots.P.filter (fun y => sref i (wact L.reverse y) ∈ E8negP)
        = (E8posRoots.P.filter (fun y => wact L.reverse y ∈ E8negP)).erase
            (- wact L (alpha i)) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hyP, hcond⟩
        refine ⟨?_, hyP, ?_⟩
        · intro hyeq
          rw [hyeq, hrevneg, sref_neg_alpha] at hcond
          exact not_mem_E8negP_of_memP (alpha i) halP hcond
        · rcases hhroot y hyP with hypos | hyneg
          · have h1 : wact L.reverse y = alpha i :=
              (sref_mem_negP_iff i (wact L.reverse y) hypos).mp hcond
            have h2 : y = wact L (alpha i) := hkey2 y h1
            rw [h2] at hyP
            exact absurd hyP (not_memP_of_mem_E8negP _ hgN)
          · exact hyneg
      · rintro ⟨hne, hyP, hyneg⟩
        refine ⟨hyP, ?_⟩
        have hne' : wact L.reverse y ≠ - alpha i := by
          intro hcon
          exact hne (hkey y hcon)
        exact (sref_mem_negP_iff_of_mem_negP i (wact L.reverse y) hyneg).mpr hne'
    rw [hset]
    have hsum := Finset.sum_erase_add
      (E8posRoots.P.filter (fun y => wact L.reverse y ∈ E8negP)) (fun y => y) hzF2
    rw [← hsum]
    abel

lemma sref_rhoZ (i : Fin 8) : sref i rhoZ = rhoZ - alpha i := by
  funext j
  simp only [sref_apply, rhoZ, Pi.sub_apply, alpha_apply]
  ring

/-- **The Weyl-group "sum of positive roots sent negative" formula.**  For a word `L` of simple reflections with associated action `wact L` on the `ω`-coordinates of the weight lattice, writing `N(w) = {y ∈ Φ⁺ : w y ∈ Φ⁻}` for the set of positive roots (`E8posRoots.P`) sent to negative roots, one has `ρ - wρ = ∑_{y ∈ N(w)} y`.  Equivalently, with `w⁻¹` acting on `P` (the word `L.reverse`), the difference `ρ - wρ` equals the sum of the positive roots `y` for which `wact L.reverse y` is again a negative root (`-y' ∈ P`). -/
theorem E8_rho_sub_wact_rho_eq_sum (L : List (Fin 8)) :
    Commons.LinearAlgebra.Matrix.Cartan.rhoZ - Commons.LinearAlgebra.Matrix.Cartan.wact L Commons.LinearAlgebra.Matrix.Cartan.rhoZ
      = ∑ y ∈ (E8posRoots.P.filter (fun y => -(Commons.LinearAlgebra.Matrix.Cartan.wact L.reverse y) ∈ E8posRoots.P)), y := by
  induction L with
  | nil =>
      have hempty : E8posRoots.P.filter
          (fun y => -(wact ([] : List (Fin 8)).reverse y) ∈ E8posRoots.P) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro y hy hcon
        rw [show wact ([] : List (Fin 8)).reverse y = y from rfl] at hcon
        exact not_mem_E8negP_of_memP y hy ((mem_E8negP y).mpr hcon)
      rw [hempty]
      simp
  | cons i L' ih =>
      rw [rho_step i L']
      rw [← ih]
      have hL : rhoZ - wact (i :: L') rhoZ = (rhoZ - wact L' rhoZ) + wact L' (alpha i) := by
        rw [wact_cons, sref_rhoZ, wact_sub']
        abel
      rw [hL]

end Commons.LinearAlgebra.Matrix.Cartan

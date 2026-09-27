import Mathlib
import Submission.Work.KT.idem_close_conj
import Submission.Work.KT.homotopy_inv
import Submission.Work.KT.Dim2.exists_eval_units

namespace Work.KT.Dim2

open Matrix ContinuousMap Filter

open scoped Topology

noncomputable section

/-- A path of idempotent matrices over `C(X,ℂ)` (measured with the `L∞` operator norm) is
conjugate at its endpoints. -/
theorem conj_of_path_mat {X : Type} [TopologicalSpace X] [CompactSpace X] {n : ℕ}
    (γ : unitInterval → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hγ : ∀ t : unitInterval, ∀ c : NNReal, 0 < c →
        ∀ᶠ s in 𝓝 t, homInvMatNorm (γ s - γ t) < c)
    (hidem : ∀ t, γ t * γ t = γ t) :
    ∃ u : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ,
      (u : Matrix (Fin n) (Fin n) C(X, ℂ)) * γ 1 = γ 0 * (u : Matrix (Fin n) (Fin n) C(X, ℂ)) := by
  let Conj : unitInterval → unitInterval → Prop := fun s t =>
    ∃ u : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ,
      (u : Matrix (Fin n) (Fin n) C(X, ℂ)) * γ t = γ s * (u : Matrix (Fin n) (Fin n) C(X, ℂ))
  have hrefl : ∀ t, Conj t t := fun t => ⟨1, by simp⟩
  have htrans : ∀ ⦃a b c⦄, Conj a b → Conj b c → Conj a c := by
    rintro a b c ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨u * v, ?_⟩
    rw [Units.val_mul]
    calc (↑u * ↑v) * γ c = ↑u * (↑v * γ c) := by rw [mul_assoc]
      _ = ↑u * (γ b * ↑v) := by rw [hv]
      _ = (↑u * γ b) * ↑v := by rw [mul_assoc]
      _ = (γ a * ↑u) * ↑v := by rw [hu]
      _ = γ a * (↑u * ↑v) := by rw [mul_assoc]
  have hsymm : ∀ ⦃a b⦄, Conj a b → Conj b a := by
    rintro a b ⟨u, hu⟩
    have h1 : (u : Matrix (Fin n) (Fin n) C(X, ℂ)) * γ b * (↑(u⁻¹) : Matrix (Fin n) (Fin n) C(X, ℂ))
        = γ a := by rw [hu, mul_assoc, Units.mul_inv, mul_one]
    refine ⟨u⁻¹, ?_⟩
    simp only [← h1]
    simp only [← mul_assoc, Units.inv_mul, one_mul]
  have hlocal : ∀ t : unitInterval, ∀ᶠ s in 𝓝 t, Conj t s := by
    intro t
    have hpos : (0 : NNReal) < (homInvMatNorm (2 * γ t - 1) + 1)⁻¹ :=
      inv_pos.mpr (by positivity)
    filter_upwards [hγ t ((homInvMatNorm (2 * γ t - 1) + 1)⁻¹) hpos] with s hs
    refine idem_close_conj_of_isUnit (hidem t) (hidem s) ?_
    have hlt : homInvMatNorm (-((2 * γ t - 1) * (γ s - γ t))) < 1 := by
      rw [homInvMatNorm_neg]
      calc homInvMatNorm ((2 * γ t - 1) * (γ s - γ t))
          ≤ homInvMatNorm (2 * γ t - 1) * homInvMatNorm (γ s - γ t) := homInvMatNorm_mul_le _ _
        _ ≤ homInvMatNorm (2 * γ t - 1) * (homInvMatNorm (2 * γ t - 1) + 1)⁻¹ :=
              mul_le_mul_of_nonneg_left (le_of_lt hs) (by positivity)
        _ < 1 := by
              rw [← NNReal.coe_lt_coe, NNReal.coe_one, NNReal.coe_mul, NNReal.coe_inv,
                NNReal.coe_add, NNReal.coe_one]
              rw [← div_eq_mul_inv, div_lt_one (by positivity)]
              linarith
    have := isUnit_one_sub_of_matNorm_lt_one (-((2 * γ t - 1) * (γ s - γ t))) hlt
    simpa using this
  have hopen : IsOpen {t : unitInterval | Conj 0 t} := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hlocal t] with s hs
    exact htrans ht hs
  have hclosed : IsOpen {t : unitInterval | Conj 0 t}ᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    filter_upwards [hlocal t] with s hs
    intro hsT
    exact ht (htrans hsT (hsymm hs))
  have hsub : (Set.univ : Set unitInterval) ⊆ {t : unitInterval | Conj 0 t} ∪ {t : unitInterval | Conj 0 t}ᶜ := by
    intro t _
    by_cases h : Conj 0 t
    · exact Or.inl h
    · exact Or.inr h
  have hdisj : Disjoint {t : unitInterval | Conj 0 t} {t : unitInterval | Conj 0 t}ᶜ :=
    disjoint_compl_right
  rcases PreconnectedSpace.isPreconnected_univ.subset_or_subset hopen hclosed hdisj hsub with h | h
  · exact h (Set.mem_univ 1)
  · exact absurd (hrefl 0) (h (Set.mem_univ 0))

theorem idem_conj_of_contractible (X : Type) [TopologicalSpace X] [CompactSpace X]
    [ContractibleSpace X] (n : ℕ) (p : C(X, Matrix (Fin n) (Fin n) ℂ))
    (hp : ∀ x, p x * p x = p x) :
    ∃ (e : Matrix (Fin n) (Fin n) ℂ) (u v : C(X, Matrix (Fin n) (Fin n) ℂ)),
      e * e = e ∧ (∀ x, u x * v x = 1 ∧ v x * u x = 1) ∧ (∀ x, u x * p x * v x = e) := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x0, hhom⟩ := id_nullhomotopic X
    obtain ⟨Hk⟩ := hhom.symm
    let swapI : C(X × unitInterval, unitInterval × X) := ⟨fun q => (q.2, q.1), by fun_prop⟩
    let K : C(X × unitInterval, X) := Hk.toContinuousMap.comp swapI
    let P : C(X × unitInterval, Matrix (Fin n) (Fin n) ℂ) := p.comp K
    have hK_zero : ∀ x, K (x, 0) = x0 := by
      intro x
      show Hk.toContinuousMap (0, x) = x0
      exact Hk.map_zero_left x
    have hK_one : ∀ x, K (x, 1) = x := by
      intro x
      show Hk.toContinuousMap (1, x) = x
      exact Hk.map_one_left x
    let entry : Fin n → Fin n → C(unitInterval, C(X, ℂ)) := fun i j =>
      ContinuousMap.curry ⟨fun q : unitInterval × X => P (q.2, q.1) i j,
        (P.continuous.matrix_elem i j).comp (continuous_snd.prodMk continuous_fst)⟩
    have entry_apply : ∀ (i j : Fin n) (t : unitInterval) (x : X),
        entry i j t x = P (x, t) i j := by
      intro i j t x
      rw [show entry i j = ContinuousMap.curry ⟨fun q : unitInterval × X => P (q.2, q.1) i j,
          (P.continuous.matrix_elem i j).comp (continuous_snd.prodMk continuous_fst)⟩ from rfl]
      rw [ContinuousMap.curry_apply]
      rfl
    let γ : unitInterval → Matrix (Fin n) (Fin n) C(X, ℂ) := fun t => Matrix.of (fun i j => entry i j t)
    have hγ_apply : ∀ (t : unitInterval) (i j : Fin n), γ t i j = entry i j t := by
      intro t i j; rfl
    have hidem : ∀ t, γ t * γ t = γ t := by
      intro t
      ext i j x
      simp only [Matrix.mul_apply, ContinuousMap.mul_apply, ContinuousMap.sum_apply]
      simp only [hγ_apply, entry_apply, P, ContinuousMap.comp_apply]
      rw [← Matrix.mul_apply, hp (K (x, t))]
    have hγ : ∀ t : unitInterval, ∀ c : NNReal, 0 < c →
        ∀ᶠ s in 𝓝 t, homInvMatNorm (γ s - γ t) < c := by
      intro t0 c hc
      set e : NNReal := c / ((n : NNReal) + 1) with he
      have hepos : 0 < e := by rw [he]; exact div_pos hc (by positivity)
      have hE : ∀ᶠ s in 𝓝 t0, ∀ i j : Fin n, ‖(γ s - γ t0) i j‖₊ ≤ e := by
        rw [Filter.eventually_all]
        intro i
        rw [Filter.eventually_all]
        intro j
        have hcont : ∀ᶠ s in 𝓝 t0, dist (entry i j s) (entry i j t0) < (e : ℝ) :=
          Metric.tendsto_nhds.mp ((entry i j).continuous.continuousAt (x := t0)) _
            (by exact_mod_cast hepos)
        filter_upwards [hcont] with s hs
        rw [dist_eq_norm] at hs
        rw [show (γ s - γ t0) i j = entry i j s - entry i j t0 by
              simp [γ, Matrix.of_apply]]
        rw [← NNReal.coe_le_coe, coe_nnnorm]
        exact le_of_lt hs
      filter_upwards [hE] with s hs
      calc homInvMatNorm (γ s - γ t0)
          ≤ (n : NNReal) * e := homInvMatNorm_le_card_mul _ hs
        _ < c := by
            have hcR : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
            rw [← NNReal.coe_lt_coe]
            simp only [he, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_div,
              NNReal.coe_add, NNReal.coe_one]
            rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
            nlinarith [hcR]
    obtain ⟨u, hu⟩ := conj_of_path_mat γ hγ hidem
    obtain ⟨u', v', hu'e, hv'e, huv⟩ := exists_eval_units n u
    have evalMat_apply : ∀ (x : X) (M : Matrix (Fin n) (Fin n) C(X, ℂ)) (i j : Fin n),
        RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom M i j = M i j x := by
      intro x M i j
      rw [RingHom.mapMatrix_apply, Matrix.map_apply]
      exact ContinuousMap.evalAlgHom_apply ℂ ℂ x (M i j)
    have hγ0 : ∀ x, RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom (γ 0) = p x0 := by
      intro x
      ext i j
      rw [evalMat_apply, show γ 0 i j = entry i j 0 from rfl]
      show ((entry i j) 0) x = p x0 i j
      rw [entry_apply]
      show P (x, 0) i j = p x0 i j
      rw [show P (x, 0) = p (K (x, 0)) from ContinuousMap.comp_apply p K (x, 0), hK_zero]
    have hγ1 : ∀ x, RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom (γ 1) = p x := by
      intro x
      ext i j
      rw [evalMat_apply, show γ 1 i j = entry i j 1 from rfl]
      show ((entry i j) 1) x = p x i j
      rw [entry_apply]
      show P (x, 1) i j = p x i j
      rw [show P (x, 1) = p (K (x, 1)) from ContinuousMap.comp_apply p K (x, 1), hK_one]
    refine ⟨p x0, u', v', hp x0, ?_, ?_⟩
    · intro x; exact huv x
    · intro x
      have hconj_x : u' x * p x = p x0 * u' x := by
        have hmap := congrArg (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom) hu
        rw [map_mul, map_mul] at hmap
        rw [hγ1 x, hγ0 x, ← hu'e x] at hmap
        exact hmap
      calc u' x * p x * v' x = (u' x * p x) * v' x := rfl
        _ = (p x0 * u' x) * v' x := by rw [hconj_x]
        _ = p x0 * (u' x * v' x) := by rw [mul_assoc]
        _ = p x0 := by rw [(huv x).1, mul_one]
  ·
    exact ⟨0, ContinuousMap.const X (0 : Matrix (Fin n) (Fin n) ℂ),
        ContinuousMap.const X (0 : Matrix (Fin n) (Fin n) ℂ), by simp,
      fun x => (hX ⟨x⟩).elim, fun x => (hX ⟨x⟩).elim⟩

end

end Work.KT.Dim2

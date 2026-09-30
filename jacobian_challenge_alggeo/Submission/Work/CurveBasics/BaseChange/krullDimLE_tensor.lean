import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveBasics.BaseChange

open scoped TensorProduct

/-- Integral extensions do not increase the ring Krull dimension. -/
theorem ringKrullDim_le_of_isIntegral_aux {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim, ringKrullDim]
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) fun x y hxy => ?_
  exact Ideal.IsIntegral.under_lt_under hxy

/-- Integral injective extensions do not decrease the ring Krull dimension. -/
theorem ringKrullDim_le_of_isIntegral_of_injective_aux {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] (h : Function.Injective (algebraMap R S)) :
    ringKrullDim R ≤ ringKrullDim S := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    RingHom.IsIntegral.comap_surjective (algebraMap_isIntegral_iff.mpr inferInstance) h
  by_cases hne : Nonempty (PrimeSpectrum R)
  · haveI hR : Nontrivial R := PrimeSpectrum.nonempty_iff_nontrivial.mp hne
    haveI hS : Nontrivial S := h.nontrivial
    haveI : Nonempty (PrimeSpectrum S) := PrimeSpectrum.nonempty_iff_nontrivial.mpr hS
    rw [ringKrullDim, ringKrullDim, Order.krullDim_eq_iSup_length (α := PrimeSpectrum R),
      Order.krullDim_eq_iSup_length (α := PrimeSpectrum S)]
    simp only [WithBot.coe_le_coe]
    refine iSup_le fun l => ?_
    obtain ⟨Q, hQ⟩ := hsurj l.head
    have hLO : Q.asIdeal.LiesOver l.head.asIdeal :=
      ⟨by rw [Ideal.under_def, ← PrimeSpectrum.comap_asIdeal, hQ]⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l Q.asIdeal
    rw [← hlen]
    exact le_iSup (fun l' : LTSeries (PrimeSpectrum S) => ((l'.length : ℕ∞))) L
  · rw [ringKrullDim]
    have hbot : Order.krullDim (PrimeSpectrum R) = ⊥ :=
      Order.krullDim_eq_bot_iff.mpr ⟨fun x => hne ⟨x⟩⟩
    rw [hbot]
    exact bot_le

theorem krullDimLE_tensor {k F R : Type*} [Field k] [Field F] [Algebra k F] [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] {n : ℕ} (h : Ring.KrullDimLE n R) :
    Ring.KrullDimLE n (TensorProduct k R F) := by
  rw [Ring.krullDimLE_iff] at h ⊢
  by_cases hR : Nontrivial R
  · obtain ⟨s, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg k R
    letI : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
    haveI hint : Algebra.IsIntegral (MvPolynomial (Fin s) k) R := ⟨hg_int⟩
    have hunj : Function.Injective (algebraMap (MvPolynomial (Fin s) k) R) := hg_inj
    have hdimA : ringKrullDim (MvPolynomial (Fin s) k) = (s : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := k) (ι := Fin s)]
      simp
    have hs_le : (s : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
      rw [← hdimA]
      exact (ringKrullDim_le_of_isIntegral_of_injective_aux hunj).trans h
    have hdimT : ringKrullDim (TensorProduct k (MvPolynomial (Fin s) k) F) = (s : WithBot ℕ∞) := by
      rw [ringKrullDim_eq_of_ringEquiv
        ((Algebra.TensorProduct.comm k (MvPolynomial (Fin s) k) F).toRingEquiv.trans
          (MvPolynomial.scalarRTensorAlgEquiv (R := k) (N := F) (σ := Fin s)).toRingEquiv)]
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := F) (ι := Fin s)]
      simp
    letI : Algebra (TensorProduct k (MvPolynomial (Fin s) k) F) (TensorProduct k R F) :=
      (Algebra.TensorProduct.map g (AlgHom.id k F)).toRingHom.toAlgebra
    haveI hbase : Algebra.IsIntegral (TensorProduct k (MvPolynomial (Fin s) k) F)
        (TensorProduct k R F) := by
      rw [Algebra.isIntegral_def]
      intro x
      refine TensorProduct.inductionOn x ?_ ?_
      · intro a b
        have h1 : IsIntegral (TensorProduct k (MvPolynomial (Fin s) k) F)
            (a ⊗ₜ[k] (1 : F)) := by
          have key := IsIntegral.map_of_comp_eq
            (algebraMap (MvPolynomial (Fin s) k) (TensorProduct k (MvPolynomial (Fin s) k) F))
            ((Algebra.TensorProduct.includeLeft : R →ₐ[k] TensorProduct k R F).toRingHom)
            (by
              refine RingHom.ext fun z => ?_
              simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.map_tmul,
                Algebra.TensorProduct.includeLeft_apply])
            (Algebra.IsIntegral.isIntegral a)
          simpa [Algebra.TensorProduct.includeLeft_apply] using key
        have h2 : IsIntegral (TensorProduct k (MvPolynomial (Fin s) k) F)
            ((1 : R) ⊗ₜ[k] b) := by
          have hφ : (Algebra.TensorProduct.map g (AlgHom.id k F))
              ((1 : MvPolynomial (Fin s) k) ⊗ₜ[k] b)
                = ((1 : R) ⊗ₜ[k] b) := by
            rw [Algebra.TensorProduct.map_tmul]; simp
          rw [← hφ]
          exact isIntegral_algebraMap (x := ((1 : MvPolynomial (Fin s) k) ⊗ₜ[k] b))
        have hmul : (a ⊗ₜ[k] b)
            = (a ⊗ₜ[k] (1 : F)) * ((1 : R) ⊗ₜ[k] b) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul]; simp
        rw [hmul]
        exact h1.mul h2
      · intro x y hx hy
        exact hx.add hy
    have hstep1 : ringKrullDim (TensorProduct k R F)
        ≤ ringKrullDim (TensorProduct k (MvPolynomial (Fin s) k) F) :=
      ringKrullDim_le_of_isIntegral_aux
    exact hstep1.trans (hdimT ▸ hs_le)
  · haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    haveI : Subsingleton (TensorProduct k R F) := inferInstance
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le

end Work.CurveBasics.BaseChange

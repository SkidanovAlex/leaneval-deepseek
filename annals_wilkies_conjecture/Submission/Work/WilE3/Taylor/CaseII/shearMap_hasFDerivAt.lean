import Mathlib

namespace Work.WilE3.Taylor.CaseII

theorem shearMap_hasFDerivAt {k : ℕ} (i₀ : Fin k) (x : Fin k → ℝ) (s : ℝ)
    (a b : (Fin k → ℝ) → (Fin k → ℝ)) (φ : (Fin k → ℝ) → ℝ)
    (ha : HasFDerivAt a (fderiv ℝ a x) x) (hb : HasFDerivAt b (fderiv ℝ b x) x)
    (hφ : HasFDerivAt φ (fderiv ℝ φ x) x) :
    HasFDerivAt (fun p : (Fin k → ℝ) × ℝ =>
        (fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2), φ p.1))
      ((ContinuousLinearMap.pi (fun i : Fin k =>
          if i = i₀ then ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ
          else -(((ContinuousLinearMap.proj i).comp (fderiv ℝ a x)).comp
                    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                  + s • ((ContinuousLinearMap.proj i).comp (fderiv ℝ b x)).comp
                    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                  + (b x i) • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ))).prod
        ((fderiv ℝ φ x).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)))
      (x, s) := by
  have hfst : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => p.1)
      (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ) (x, s) :=
    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => p.2)
      (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ) (x, s) :=
    (ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ).hasFDerivAt
  have hphi : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => φ p.1)
      ((fderiv ℝ φ x).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)) (x, s) :=
    hφ.comp (x, s) hfst
  have hcomp : ∀ i : Fin k,
      HasFDerivAt (fun p : (Fin k → ℝ) × ℝ =>
          if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2))
        (if i = i₀ then ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ
          else -(((ContinuousLinearMap.proj i).comp (fderiv ℝ a x)).comp
                    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                  + s • ((ContinuousLinearMap.proj i).comp (fderiv ℝ b x)).comp
                    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                  + (b x i) • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ)) (x, s) := by
    intro i
    by_cases h : i = i₀
    · simp only [ite_eq_left h]
      exact hsnd
    · simp only [ite_eq_right h]
      have h1a : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => a p.1)
          ((fderiv ℝ a x).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)) (x, s) :=
        ha.comp (x, s) hfst
      have h1b : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => b p.1)
          ((fderiv ℝ b x).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)) (x, s) :=
        hb.comp (x, s) hfst
      have hpa : HasFDerivAt (fun v : Fin k → ℝ => v i)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) (a x) :=
        ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) (x := a x)
      have hpb : HasFDerivAt (fun v : Fin k → ℝ => v i)
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) (b x) :=
        ContinuousLinearMap.hasFDerivAt
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i) (x := b x)
      have hAi := hpa.comp (x, s) h1a
      rw [← ContinuousLinearMap.comp_assoc] at hAi
      have hBi := hpb.comp (x, s) h1b
      rw [← ContinuousLinearMap.comp_assoc] at hBi
      have hprod : HasFDerivAt (fun p : (Fin k → ℝ) × ℝ => b p.1 i * p.2)
          (s • ((ContinuousLinearMap.proj i).comp (fderiv ℝ b x)).comp
                (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
            + (b x i) • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ) (x, s) := by
        have h := hBi.mul hsnd
        rw [add_comm] at h
        exact h
      have hsum : HasFDerivAt
          (fun p : (Fin k → ℝ) × ℝ => a p.1 i + b p.1 i * p.2)
          (((ContinuousLinearMap.proj i).comp (fderiv ℝ a x)).comp
                (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
            + (s • ((ContinuousLinearMap.proj i).comp (fderiv ℝ b x)).comp
                  (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
              + (b x i) • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ)) (x, s) :=
        hAi.add hprod
      have hneg := hsum.neg
      rw [← add_assoc] at hneg
      exact hneg
  have hvec : HasFDerivAt
      (fun p : (Fin k → ℝ) × ℝ =>
        fun i : Fin k => if i = i₀ then p.2 else -(a p.1 i + b p.1 i * p.2))
      (ContinuousLinearMap.pi (fun i : Fin k =>
          if i = i₀ then ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ
          else -(((ContinuousLinearMap.proj i).comp (fderiv ℝ a x)).comp
                    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                  + s • ((ContinuousLinearMap.proj i).comp (fderiv ℝ b x)).comp
                    (ContinuousLinearMap.fst ℝ (Fin k → ℝ) ℝ)
                  + (b x i) • ContinuousLinearMap.snd ℝ (Fin k → ℝ) ℝ))) (x, s) :=
    hasFDerivAt_pi.mpr hcomp
  exact hvec.prodMk hphi

end Work.WilE3.Taylor.CaseII

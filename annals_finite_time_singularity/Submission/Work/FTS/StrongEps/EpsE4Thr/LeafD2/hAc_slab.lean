import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.XStep

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.LeafD2

theorem hAc_slab {α C₀ Ce Cs R ε δ Cpt : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hC₀ : 0 < C₀)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hδ : 0 < δ) (hR : 0 < R) (hsm0 : Work.FTS.EllipticEst.SmoothOpen h₀)
    (hlim : ∀ τ ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ))
    (hvol : ∀ z θ τ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → τ ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ z θ τ
        = h₀ z θ + ∫ s in (0 : ℝ)..τ,
            Work.FTS.EpsEngine.Feps α ρ ε Φs E
              (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) s) z θ)
    (hCpt : 0 ≤ Cpt)
    (hpt : ∀ u v : Work.FTS.Galerkin.Fn, Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) u →
      Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.EpsEngine.Feps α ρ ε Φs E u z θ - Work.FTS.EpsEngine.Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)))
    (hLip : ∃ L' : ℝ, 0 < L' ∧ ∀ σ ∈ Set.Icc 0 δ, ∀ τ ∈ Set.Icc 0 δ,
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) σ z θ
          - Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) τ z θ)
        ≤ L' * (σ - τ) ^ 2) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.FTS.EpsEngine.Feps α ρ ε Φs E
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀) p.2.2)
          p.1 p.2.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) ×ˢ Set.Icc 0 δ) := by
  -- The map is `p ↦ Feps (u_{p.2.2}) p.1 p.2.1`.  It is
  --  * continuous in `(z, θ) = (p.1, p.2.1)` at every fixed time `τ = p.2.2 ∈ Icc 0 δ`
  --    (`EpsEngine.continuousOn_Feps_of_XBall`, using `hlim`),
  --  * Lipschitz in `τ`, uniformly in `(z, θ) ∈ Ioi 0 ×ˢ Ioo 0 (π/2)`, with constant
  --    `Cpt · √L'` (`hpt` against `hLip`),
  -- so the joint continuity is an `ε/2`-argument.
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro e he
  -- abbreviation: the limit family of the Picard scheme
  let LF : Work.FTS.Galerkin.Fam :=
    Work.FTS.StrongEps.EpsLocalPStar.limFam (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀
  have hz : 0 < p.1 := hp.1
  have hθ1 : 0 < p.2.1 := hp.2.1.1
  have hθ2 : p.2.1 < Real.pi / 2 := hp.2.1.2
  have hτp : p.2.2 ∈ Set.Icc (0 : ℝ) δ := hp.2.2
  -- ## the Lipschitz-in-`τ` data
  obtain ⟨L', hL'pos, hLip'⟩ := hLip
  have hK : 0 ≤ Cpt * Real.sqrt L' := mul_nonneg hCpt (Real.sqrt_nonneg L')
  have hden : 0 < 2 * (Cpt * Real.sqrt L' + 1) := by linarith
  have hδe : 0 < e / (2 * (Cpt * Real.sqrt L' + 1)) := div_pos he hden
  -- ## continuity in `(z, θ)` at the fixed slice `τ = p.2.2`
  have hcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice LF p.2.2) q.1 q.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
      (u := Work.FTS.Galerkin.slice LF p.2.2) hα hρ hε hEll hstar (hlim p.2.2 hτp)).1
  have hmem : (p.1, p.2.1) ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨hz, hθ1, hθ2⟩
  have hopen : IsOpen (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)) :=
    isOpen_Ioi.prod isOpen_Ioo
  have hca : ContinuousAt (fun q : ℝ × ℝ => Work.FTS.EpsEngine.Feps α ρ ε Φs E
      (Work.FTS.Galerkin.slice LF p.2.2) q.1 q.2) (p.1, p.2.1) :=
    (hcont (p.1, p.2.1) hmem).continuousAt (hopen.mem_nhds hmem)
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.1 hca (e / 2) (by linarith)
  refine ⟨min δ₂ (e / (2 * (Cpt * Real.sqrt L' + 1))), lt_min hδ₂pos hδe, ?_⟩
  intro x hx hxd
  have hx1 : 0 < x.1 := hx.1
  have hxθ1 : 0 < x.2.1 := hx.2.1.1
  have hxθ2 : x.2.1 < Real.pi / 2 := hx.2.1.2
  have hxτ : x.2.2 ∈ Set.Icc (0 : ℝ) δ := hx.2.2
  -- ## the time difference is small
  have hdτ : |x.2.2 - p.2.2| < e / (2 * (Cpt * Real.sqrt L' + 1)) := by
    have hcoord : |x.2.2 - p.2.2| ≤ dist x p := by
      have h4 : dist x p
          = max (dist x.1 p.1) (max (dist x.2.1 p.2.1) (dist x.2.2 p.2.2)) := by
        simp only [Prod.dist_eq]
      have h3 : dist x.2.2 p.2.2 = |x.2.2 - p.2.2| := Real.dist_eq _ _
      rw [h4, h3]
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hcoord (lt_of_lt_of_le hxd (min_le_right _ _))
  -- ## the `(z, θ)`-difference is small
  have hdzθ : dist (x.1, x.2.1) (p.1, p.2.1) < δ₂ := by
    have h4 : dist x p
        = max (dist x.1 p.1) (max (dist x.2.1 p.2.1) (dist x.2.2 p.2.2)) := by
      simp only [Prod.dist_eq]
    have h5 : dist (x.1, x.2.1) (p.1, p.2.1)
        = max (dist x.1 p.1) (dist x.2.1 p.2.1) := by
      simp only [Prod.dist_eq]
    have hle : dist (x.1, x.2.1) (p.1, p.2.1) ≤ dist x p := by
      rw [h5, h4]
      exact max_le_max le_rfl (le_max_left _ _)
    exact lt_of_le_of_lt hle (lt_of_lt_of_le hxd (min_le_left _ _))
  -- ## the two `e/2`-pieces
  have he2 : |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1
      - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) p.1 p.2.1|
      < e / 2 := by
    simpa only [Real.dist_eq] using hδ₂ hdzθ
  have he1 : |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF x.2.2) x.1 x.2.1
      - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1|
      < e / 2 := by
    have hpt' := hpt (Work.FTS.Galerkin.slice LF x.2.2) (Work.FTS.Galerkin.slice LF p.2.2)
      (hlim x.2.2 hxτ) (hlim p.2.2 hτp) x.1 x.2.1 hx1 hxθ1 hxθ2
    have hdiff : Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ)
        ≤ L' * (x.2.2 - p.2.2) ^ 2 := (hLip' x.2.2 hxτ p.2.2 hτp).2
    have hsqrt : Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
        ≤ Real.sqrt L' * |x.2.2 - p.2.2| := by
      calc Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
              Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
          ≤ Real.sqrt (L' * (x.2.2 - p.2.2) ^ 2) := Real.sqrt_le_sqrt hdiff
        _ = Real.sqrt L' * Real.sqrt ((x.2.2 - p.2.2) ^ 2) := Real.sqrt_mul hL'pos.le _
        _ = Real.sqrt L' * |x.2.2 - p.2.2| := by rw [Real.sqrt_sq_eq_abs]
    have hmain : Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
        < e / 2 := by
      calc Cpt * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ =>
              Work.FTS.Galerkin.slice LF x.2.2 z θ - Work.FTS.Galerkin.slice LF p.2.2 z θ))
          ≤ Cpt * (Real.sqrt L' * |x.2.2 - p.2.2|) := mul_le_mul_of_nonneg_left hsqrt hCpt
        _ = Cpt * Real.sqrt L' * |x.2.2 - p.2.2| := by ring
        _ ≤ Cpt * Real.sqrt L' * (e / (2 * (Cpt * Real.sqrt L' + 1))) :=
              mul_le_mul_of_nonneg_left (le_of_lt hdτ) hK
        _ < e / 2 := by
              rw [← mul_div_assoc]
              rw [div_lt_iff₀ hden]
              nlinarith [he]
    exact lt_of_le_of_lt hpt' hmain
  -- ## triangle inequality
  rw [Real.dist_eq]
  calc |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF x.2.2) x.1 x.2.1
        - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) p.1 p.2.1|
      ≤ |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF x.2.2) x.1 x.2.1
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1|
        + |Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) x.1 x.2.1
          - Work.FTS.EpsEngine.Feps α ρ ε Φs E (Work.FTS.Galerkin.slice LF p.2.2) p.1 p.2.1| :=
          abs_sub_le _ _ _
    _ < e / 2 + e / 2 := add_lt_add he1 he2
    _ = e := by ring

end Work.FTS.StrongEps.EpsE4Thr.LeafD2

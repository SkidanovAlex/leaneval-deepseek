import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.R1b.General
import Submission.Work.FTS.RegPkgGal.R1b.Locals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R1b

open Set Filter Topology MeasureTheory
open scoped Topology Real

set_option autoImplicit false

/-! ## The two branches are `C¹` on `z > 0` -/

section Branches

variable {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}

/-- `tauDer` is `C¹` on `z > 0`. -/
theorem tauDer_contDiffOn
    (hd1 : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContDiffOn ℝ 1 (tauDer g θ) (Ioi 0) := by
  have hmap : MapsTo (fun z : ℝ => (z, (0:ℝ))) (Ioi 0) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    fun z hz => ⟨hz, by norm_num⟩
  have hι : ContDiffOn ℝ 1 (fun z : ℝ => (z, (0:ℝ))) (Ioi 0) :=
    contDiffOn_id.prodMk contDiffOn_const
  have h := hd1.comp hι hmap
  change ContDiffOn ℝ 1 (fun z : ℝ => deriv (fun s => g z θ s) 0) (Ioi 0)
  exact h

/-- `jetFn` is `C¹` on `z > 0`. -/
theorem jetFn_contDiffOn
    (hbase : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)))
    (hdd : ContDiffOn ℝ 1 (tauDerFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := by
  have hmap : MapsTo (fun q : ℝ × ℝ => (q.1, (0:ℝ))) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := fun q hq => ⟨hq.1, by norm_num⟩
  have hι : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => (q.1, (0:ℝ))) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    contDiffOn_fst.prodMk contDiffOn_const
  have h1 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => baseFn g θ (q.1, 0)) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    hbase.comp hι hmap
  have h2 : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => q.2 * tauDerFn g θ q) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) :=
    contDiffOn_snd.mul hdd
  refine (h1.add h2).congr (fun q _ => ?_)
  obtain ⟨z, τ⟩ := q
  simp only [jetFn_apply, baseFn_apply, tauDerFn_apply, Pi.add_apply]

/-- A `C¹` function on an open set has a Fréchet derivative at each point of the set. -/
theorem hasFDerivAt_of_contDiffOn_one {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : IsOpen s)
    (hf : ContDiffOn ℝ 1 f s) {x : ℝ × ℝ} (hx : x ∈ s) :
    HasFDerivAt f (fderiv ℝ f x) x :=
  ((hf.contDiffAt (hs.mem_nhds hx)).differentiableAt one_ne_zero).hasFDerivAt

/-- The `τ`-partial derivative of the jet. -/
theorem deriv_jetFn_snd (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) (z τ : ℝ) :
    deriv (fun t => jetFn g θ (z, t)) τ = tauDer g θ z := by
  have hfun : (fun t : ℝ => jetFn g θ (z, t)) = fun t : ℝ => g z θ 0 + t * tauDer g θ z := by
    funext t; simp only [jetFn_apply]
  rw [hfun, deriv_const_add]
  have h2 : HasDerivAt (fun t : ℝ => t * tauDer g θ z) (tauDer g θ z) τ := by
    simpa using (hasDerivAt_id τ).mul_const (tauDer g θ z)
  rw [h2.deriv]

/-- The `z`-partial derivative of the jet. -/
theorem deriv_jetFn_fst (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ}
    (hb : DifferentiableAt ℝ (fun z' => g z' θ 0) z)
    (hd : DifferentiableAt ℝ (tauDer g θ) z) :
    deriv (fun z' => jetFn g θ (z', τ)) z
      = deriv (fun z' => g z' θ 0) z + τ * deriv (tauDer g θ) z := by
  have hfun : (fun z' : ℝ => jetFn g θ (z', τ))
      = (fun z' : ℝ => g z' θ 0) + fun z' : ℝ => τ * tauDer g θ z' := by
    funext z'; simp only [Pi.add_apply, jetFn_apply]
  rw [hfun, deriv_add hb (hd.const_mul τ), deriv_const_mul τ hd]

/-- At `τ = 0` the jet and the family have the same Fréchet derivative (the jet is the
first-order Taylor expansion of the family in `τ`). -/
theorem fderiv_jetFn_eq_fderiv_baseFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z : ℝ}
    (hdj : DifferentiableAt ℝ (jetFn g θ) (z, 0))
    (hdb : DifferentiableAt ℝ (baseFn g θ) (z, 0)) :
    fderiv ℝ (jetFn g θ) (z, 0) = fderiv ℝ (baseFn g θ) (z, 0) := by
  rw [fderiv_eq_partials hdj, fderiv_eq_partials hdb]
  have h1 : deriv (fun z' : ℝ => jetFn g θ (z', (0:ℝ))) z
      = deriv (fun z' : ℝ => baseFn g θ (z', (0:ℝ))) z := by
    have ha : (fun z' : ℝ => jetFn g θ (z', (0:ℝ))) = fun z' : ℝ => g z' θ 0 := by
      funext z'; simp only [jetFn_apply, zero_mul, add_zero]
    have hb : (fun z' : ℝ => baseFn g θ (z', (0:ℝ))) = fun z' : ℝ => g z' θ 0 := by
      funext z'; simp only [baseFn_apply]
    rw [ha, hb]
  have h2 : deriv (fun s : ℝ => jetFn g θ (z, s)) (0:ℝ)
      = deriv (fun s : ℝ => baseFn g θ (z, s)) 0 := by
    rw [deriv_jetFn_snd]
    simp only [baseFn_apply, tauDer]
  rw [h1, h2]

end Branches

/-- At `τ = 0` the two branches of the candidate derivative agree. -/
theorem jetBranch_eq_baseBranch_at_zero (g : ℝ → ℝ → ℝ → ℝ) (θ z : ℝ) :
    jetBranch g θ (z, 0) = baseBranch g θ (z, 0) := by
  have h1 : (fun z' : ℝ => jetFn g θ (z', (0:ℝ))) = fun z' : ℝ => baseFn g θ (z', (0:ℝ)) := by
    funext z'; simp only [jetFn_apply, baseFn_apply, zero_mul, add_zero]
  have h2 : deriv (fun t : ℝ => jetFn g θ (z, t)) (0:ℝ)
      = deriv (fun t : ℝ => baseFn g θ (z, t)) 0 := by
    rw [deriv_jetFn_snd]
    simp only [baseFn_apply, tauDer]
  simp only [jetBranch, baseBranch]
  rw [h1, h2]

theorem extDeriv_eq_fderiv_baseFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : 0 ≤ τ) (hd : DifferentiableAt ℝ (baseFn g θ) (z, τ)) :
    extDeriv g θ (z, τ) = fderiv ℝ (baseFn g θ) (z, τ) := by
  rw [extDeriv_of_pos_of_nonneg' g θ hz hτ]
  exact (fderiv_eq_partials hd).symm

/-- The candidate derivative at `τ < 0` is the Fréchet derivative of the jet. -/
theorem extDeriv_eq_fderiv_jetFn (g : ℝ → ℝ → ℝ → ℝ) (θ : ℝ) {z τ : ℝ} (hz : 0 < z)
    (hτ : τ < 0) (hd : DifferentiableAt ℝ (jetFn g θ) (z, τ)) :
    extDeriv g θ (z, τ) = fderiv ℝ (jetFn g θ) (z, τ) := by
  rw [extDeriv_of_pos_of_neg' g θ hz hτ]
  exact (fderiv_eq_partials hd).symm

/-- **The `τ = 0` gluing** (`z > 0`): the extension is differentiable at `(z,0)` with the
candidate derivative, because the two branches have the same Fréchet derivative there. -/
theorem hasFDerivAt_extFun_join {g : ℝ → ℝ → ℝ → ℝ} {θ z : ℝ} (hz : 0 < z)
    (hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)))
    (hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    HasFDerivAt (extFun g θ) (extDeriv g θ (z, 0)) (z, 0) := by
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have hxV : (z, (0:ℝ)) ∈ Ioi 0 ×ˢ Ioi (-1) := ⟨hz, by norm_num⟩
  have hdj : DifferentiableAt ℝ (jetFn g θ) (z, 0) :=
    (hasFDerivAt_of_contDiffOn_one hVopen hjetV hxV).differentiableAt
  have hdb : DifferentiableAt ℝ (baseFn g θ) (z, 0) :=
    (hasFDerivAt_of_contDiffOn_one hVopen hbaseV hxV).differentiableAt
  have hfdeq : fderiv ℝ (jetFn g θ) (z, 0) = fderiv ℝ (baseFn g θ) (z, 0) :=
    fderiv_jetFn_eq_fderiv_baseFn g θ hdj hdb
  rw [extDeriv_eq_fderiv_baseFn g θ hz le_rfl hdb]
  have hst : ({y : ℝ × ℝ | 0 < y.1 ∧ y.2 ≤ 0} ∪ {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2})
      ∈ 𝓝 ((z, 0) : ℝ × ℝ) := by
    have heq : ({y : ℝ × ℝ | 0 < y.1 ∧ y.2 ≤ 0}
        ∪ {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2}) = {y : ℝ × ℝ | 0 < y.1} := by
      ext y; constructor
      · rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> exact h1
      · intro h1
        by_cases h2 : y.2 ≤ 0
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, le_of_lt (lt_of_not_ge h2)⟩
    rw [heq]
    exact (isOpen_Ioi.preimage continuous_fst).mem_nhds hz
  refine hasFDerivAt_of_union (f := extFun g θ) (f₁ := jetFn g θ) (f₂ := baseFn g θ)
    (L := fderiv ℝ (baseFn g θ) (z, 0)) (x := ((z, 0) : ℝ × ℝ))
    (s := {y : ℝ × ℝ | 0 < y.1 ∧ y.2 ≤ 0}) (t := {y : ℝ × ℝ | 0 < y.1 ∧ 0 ≤ y.2})
    hst ⟨hz, le_rfl⟩ ⟨hz, le_rfl⟩ ?_ ?_ ?_ ?_
  · rintro ⟨y1, y2⟩ ⟨hy1, hy2⟩
    rcases lt_or_eq_of_le hy2 with h | h
    · exact extFun_of_pos_of_neg g θ hy1 h
    · subst h
      rw [extFun_of_pos_of_nonneg g θ hy1 le_rfl, jetFn_eq_baseFn_at_zero]
  · rintro ⟨y1, y2⟩ ⟨hy1, hy2⟩
    exact extFun_of_pos_of_nonneg g θ hy1 hy2
  · have h := hasFDerivAt_of_contDiffOn_one hVopen hjetV hxV
    rw [hfdeq] at h
    exact h
  · exact hasFDerivAt_of_contDiffOn_one hVopen hbaseV hxV

/-- Continuity on `z > 0` of the `τ < 0` branch of the candidate derivative. -/
theorem continuousOn_jetBranch {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}
    (hjetV : ContDiffOn ℝ 1 (jetFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContinuousOn (jetBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := by
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have h1 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => jetFn g θ (z, q.2)) q.1)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_z_slice hVopen hjetV
  have h2 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => jetFn g θ (q.1, t)) q.2)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_t_slice hVopen hjetV
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

/-- Continuity on `z > 0` of the `τ ≥ 0` branch of the candidate derivative. -/
theorem continuousOn_baseBranch {g : ℝ → ℝ → ℝ → ℝ} {θ : ℝ}
    (hbaseV : ContDiffOn ℝ 1 (baseFn g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ))) :
    ContinuousOn (baseBranch g θ) (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := by
  have hVopen : IsOpen (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := isOpen_Ioi.prod isOpen_Ioi
  have h1 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => baseFn g θ (z, q.2)) q.1)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_z_slice hVopen hbaseV
  have h2 : ContinuousOn (fun q : ℝ × ℝ => deriv (fun t => baseFn g θ (q.1, t)) q.2)
      (Ioi (0:ℝ) ×ˢ Ioi (-1:ℝ)) := continuousOn_deriv_t_slice hVopen hbaseV
  exact (h1.smul continuousOn_const).add (h2.smul continuousOn_const)

end Work.FTS.RegPkgGal.R1b

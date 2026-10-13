import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.FstarHkAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.OpenQAng
import Submission.Work.FTS.EllipticEst.moment_relation
import Submission.Work.FTS.EllipticEst.boxIntegrable_DzIter
import Submission.Work.FTS.EllipticEst.integrableOn_slice_l2
import Submission.Work.FTS.EllipticEst.integrableOn_box_of_slice
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.PsiInt_sq_mul_w_le_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {F : ℝ → ℝ → ℝ}

/-! ## The moment relation for `B_j = F_*(D_z^j F)`

`Bmom F j z = ∫_θ D_z^j F(z,θ) sinθcos²θ dθ` is the `j`-th radial moment of `F`.  The single
analytic input of the estimate is that the moments form a *tower*: the `j`-th moment is a
primitive of `B_{j+1}(s)/s`.  This is `moment_relation` applied to `u = D_z^j F`, whose
`z`-derivative is `D_z^{j+1}F/s`. -/

/-- The `θ`-integral of `∂_z(D_z^j F)` against `sinθcos²θ` is `B_{j+1}(s)/s`. -/
theorem Bmom_deriv_integral (j : ℕ) {s : ℝ} (hs : 0 < s) :
    (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ)
      = Bmom F (j + 1) s / s := by
  have hid : ∀ θ : ℝ, Work.Spaces.pz (Work.Spaces.DzIter j F) s θ
      = Work.Spaces.DzIter (j + 1) F s θ / s := by
    intro θ
    have h1 : Work.Spaces.DzIter (j + 1) F s θ
        = s * Work.Spaces.pz (Work.Spaces.DzIter j F) s θ := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz]
    rw [h1, mul_div_cancel_left₀ _ hs.ne']
  rw [Bmom_eq_Fstar_DzIter, Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter (j + 1) F s θ / s) * Work.Elliptic.sinCos2 θ from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by rw [hid θ])]
  rw [show (fun θ : ℝ => (Work.Spaces.DzIter (j + 1) F s θ / s) * Work.Elliptic.sinCos2 θ)
      = fun θ : ℝ => (1 / s) * (Work.Spaces.DzIter (j + 1) F s θ
          * Work.Elliptic.sinCos2 θ) from by
    funext θ; ring]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **The moment tower.**  For `0 < a < b`,
`B_j(b) = B_j(a) + ∫_a^b B_{j+1}(s)/s ds`, whenever `j + 1 ≤ k`. -/
theorem BFstar_relation (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 1 ≤ k) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    Bmom F j b = Bmom F j a + ∫ s in a..b, Bmom F (j + 1) s / s := by
  have hrel := moment_relation (Work.Spaces.DzIter j F) (hF.DzIter j)
    (fun a b ha hab => boxIntegrable_DzIter α k hF hmem j hj a b ha hab)
    (fun z hz => integrableOn_DzIter_mul_sinCos2 (F := F) α k hF hmem j (by omega) hz)
    ha hab
  rw [Bmom_eq_Fstar_DzIter, Bmom_eq_Fstar_DzIter, hrel]
  congr 1
  rw [show (∫ s in Set.Icc a b, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz (Work.Spaces.DzIter j F) s θ * Work.Elliptic.sinCos2 θ))
      = ∫ s in Set.Icc a b, Bmom F (j + 1) s / s from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun s hs => Bmom_deriv_integral (F := F) j (lt_of_lt_of_le ha hs.1))]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]

/-- **The moment tower, anchored at `c`.**  For every `y > 0`,
`B_j(y) = B_j(c) + ∫_c^y B_{j+1}(s)/s ds`. -/
theorem Bmom_eq_const_add_integral (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∀ y : ℝ, 0 < y → Bmom F j y = Bmom F j c + ∫ s in c..y, Bmom F (j + 1) s / s := by
  intro y hy
  rcases lt_trichotomy y c with hlt | heq | hgt
  · have hrel := BFstar_relation α k hF hmem j hj hy hlt
    rw [hrel, intervalIntegral.integral_symm]
    ring
  · subst heq
    simp
  · exact BFstar_relation α k hF hmem j hj hc hgt

/-! ## Continuity of the moments -/

/-- The `j`-th moment is continuous on `(0,∞)`, for `j + 1 ≤ k`. -/
theorem continuousOn_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => Bmom F j z) (Set.Ioi 0) := by
  intro z hz
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hb : a < z + a := by linarith
  have hg : IntegrableOn (fun s => Bmom F (j + 1) s / s) (Set.uIcc a (z + a)) := by
    rw [Set.uIcc_of_le hb.le]
    exact integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a (z + a) ha0 hb
  have hΦ : ContinuousOn (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.uIcc a (z + a)) :=
    intervalIntegral.continuousOn_primitive_interval hg
  have hnhds : Set.uIcc a (z + a) ∈ 𝓝 z := by
    rw [Set.uIcc_of_le hb.le]
    exact Icc_mem_nhds haz (by linarith)
  have hcontΦ : ContinuousWithinAt (fun x : ℝ => ∫ s in a..x, Bmom F (j + 1) s / s)
      (Set.Ioi 0) z :=
    (hΦ.continuousAt hnhds).continuousWithinAt
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝[Set.Ioi 0] z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Bmom_eq_const_add_integral α k hF hmem j hj ha0 x hx
  have hz_e : Bmom F j z = Bmom F j a + ∫ s in a..z, Bmom F (j + 1) s / s :=
    Bmom_eq_const_add_integral α k hF hmem j hj ha0 z hz0
  exact (continuousWithinAt_const.add hcontΦ).congr_of_eventuallyEq hev hz_e

/-! ## Differentiability of the moments -/

/-- The `j`-th moment is differentiable on `(0,∞)` with derivative `B_{j+1}(z)/z`, for
`j + 2 ≤ k`. -/
theorem hasDerivAt_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun z => Bmom F j z) (Bmom F (j + 1) z / z) z := by
  have hz0 : 0 < z := hz
  set a : ℝ := z / 2 with ha_def
  have ha0 : 0 < a := by rw [ha_def]; linarith
  have haz : a < z := by rw [ha_def]; linarith
  have hcont : ContinuousAt (fun s : ℝ => Bmom F (j + 1) s / s) z :=
    ((continuousOn_Bmom α k hF hmem (j + 1) (by omega)).continuousAt
      (isOpen_Ioi.mem_nhds hz0)).div continuousAt_id (by simpa using hz0.ne')
  have hg_cont : ContinuousOn (fun s : ℝ => Bmom F (j + 1) s / s) (Set.Ioi 0) :=
    (continuousOn_Bmom α k hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun s hs => hs.ne')
  have hInt : IntervalIntegrable (fun s : ℝ => Bmom F (j + 1) s / s) volume a z := by
    rw [intervalIntegrable_iff]
    refine (integrableOn_Bmom_div α k hF hmem (j + 1) (by omega) a z ha0 haz).mono_set ?_
    intro x hx
    rw [Set.uIoc_of_le haz.le] at hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  have hder := intervalIntegral.integral_hasDerivAt_right hInt
    ((hg_cont.stronglyMeasurableAtFilter isOpen_Ioi) z hz0) hcont
  have hev : (fun x : ℝ => Bmom F j x) =ᶠ[𝓝 z]
      (fun x : ℝ => Bmom F j a + ∫ s in a..x, Bmom F (j + 1) s / s) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with x hx
    exact Bmom_eq_const_add_integral α k hF hmem j (by omega) ha0 x hx
  exact hev.hasDerivAt_iff.mpr (hder.const_add (Bmom F j a))

/-- **A.e. differentiability of the top moment.**  For `k ≥ 1`, for almost every `z > 0` the
moment `B_{k-1}` is differentiable at `z` with derivative `B_k(z)/z`. -/
theorem ae_hasDerivAt_Bmom (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      HasDerivAt (fun z => Bmom F (k - 1) z) (Bmom F k z / z) z := by
  set P : ℝ → Prop := fun x => HasDerivAt (fun x => Bmom F (k - 1) x) (Bmom F k x / x) x
    with hP
  have key : ∀ n : ℕ, ∀ᵐ x ∂(volume.restrict (Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2))),
      P x := by
    intro n
    have hpos : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hlt : (1 : ℝ) / ((n : ℝ) + 1) < (n : ℝ) + 2 := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (1 : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) + 2) := by
        have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      rw [div_lt_iff₀ h1]
      nlinarith [h2]
    have hInt : IntervalIntegrable (fun s : ℝ => Bmom F k s / s) volume
        (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by
      rw [intervalIntegrable_iff]
      refine (integrableOn_Bmom_div α k hF hmem k le_rfl _ _ hpos hlt).mono_set ?_
      intro x hx
      rw [Set.uIoc_of_le hlt.le] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have hldt := IntervalIntegrable.ae_hasDerivAt_integral hInt
    rw [show Set.uIcc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
        = Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) from Set.uIcc_of_le hlt.le] at hldt
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hldt] with x hx hxmem
    refine ((hx hxmem (1 / ((n : ℝ) + 1))
      ⟨le_rfl, hlt.le⟩).const_add (Bmom F (k - 1) (1 / ((n : ℝ) + 1)))).congr_of_eventuallyEq ?_
    filter_upwards [isOpen_Ioi.mem_nhds (lt_of_lt_of_le hpos hxmem.1)] with y hy
    have h := Bmom_eq_const_add_integral α k hF hmem (k - 1) (by omega) hpos y hy
    simpa only [Nat.sub_add_cancel hk, Nat.sub_add_cancel (show 1 ≤ k by omega)] using h
  have keynull : ∀ n : ℕ, volume {x | x ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2)
      ∧ ¬ P x} = 0 := by
    intro n
    have h := key n
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff] at h
    simpa only [not_imp] using h
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi, MeasureTheory.ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null keynull)
  intro x hx
  rw [Set.mem_setOf_eq] at hx
  obtain ⟨hx0, hxn⟩ := not_imp.mp hx
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ,
      1 / ((n : ℝ) + 1) ≤ x ∧ x ≤ (n : ℝ) + 2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge (max x (1 / x))
    refine ⟨n, ?_, ?_⟩
    · have hx1 : 1 / x ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
      have : 1 ≤ x * (n : ℝ) := by
        rw [div_le_iff₀ hx0] at hx1
        linarith
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    · have hxn' : x ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
      linarith
  exact Set.mem_iUnion.mpr ⟨n, ⟨hn1, hn2⟩, hxn⟩

/-! ## The identity `(D_z^j F_*)(z) = B_j(z)` -/

/-- **The `D_z`-iterates of the angular moment are the moments.**  For `j + 1 ≤ k` and every
`z > 0`, `radIter (B_0) j z = B_j z`. -/
theorem radIter_Bmom_eq (α : ℝ) (k : ℕ) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j + 1 ≤ k → ∀ z : ℝ, 0 < z →
      radIter (fun z => Bmom F 0 z) j z = Bmom F j z := by
  intro j
  induction j with
  | zero => intro _ z _; rfl
  | succ n ih =>
      intro hj z hz
      rw [radIter_succ]
      have hev : (radIter (fun z => Bmom F 0 z) n) =ᶠ[𝓝 z] (fun z => Bmom F n z) := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact ih (by omega) z' hz'
      rw [hev.deriv_eq, (hasDerivAt_Bmom α k hF hmem n (by omega) hz).deriv]
      field_simp

/-- **The top `D_z`-iterate**, almost everywhere: for `k ≥ 1` and almost every `z > 0`,
`radIter (B_0) k z = B_k z`. -/
theorem ae_radIter_Bmom_eq_top (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (hk : 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h1 := ae_hasDerivAt_Bmom α (m + 1) hF hmem (by omega)
  simp only [Nat.add_sub_cancel] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at h1
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [h1] with z hzimp hzmem
  have hz0 : 0 < z := hzmem
  rw [radIter_succ]
  have hev : (radIter (fun z => Bmom F 0 z) m) =ᶠ[𝓝 z] (fun z => Bmom F m z) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with z' hz'
    exact radIter_Bmom_eq α (m + 1) hF hmem m (by omega) z' hz'
  rw [hev.deriv_eq, (hzimp hzmem).deriv]
  field_simp

/-! ## The slice estimate for `F_*(F)·sin 2θ` -/

/-- **Pointwise domination of the `H^k`-integrand of `F_*(F)·sin 2θ`**, almost everywhere in
`z`.  The `D_z`-summands are the squares of the moments `PsiInt F i z` times `sin 2θ`, and the
mixed summands are the moments times the angular profiles `D_θ^i (sin 2θ)`. -/
theorem HkIntegrand_fstarSin_le_open (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
          + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k) := by
  have hid_lt : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)), ∀ i < k,
      radIter (fun z => Bmom F 0 z) i z = Bmom F i z := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz i hi
    exact radIter_Bmom_eq α k hF hmem i (by omega) z hz
  have hid_top : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      radIter (fun z => Bmom F 0 z) k z = Bmom F k z := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _
      rfl
    · exact ae_radIter_Bmom_eq_top α k hF hmem hk
  filter_upwards [hid_lt, hid_top, MeasureTheory.ae_restrict_mem measurableSet_Ioi]
    with z hlt htop hz
  intro θ hθ
  have hg : (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      = fun z θ => Bmom F 0 z * Real.sin (2 * θ) := by
    funext z θ
    rw [Bmom_zero]
  have hDz : ∀ i ≤ k, Work.Spaces.DzIter i
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        = PsiInt F i z * Real.sin (2 * θ) := by
    intro i hi
    rw [hg, DzIter_fstarSin_eq]
    congr 1
    rcases lt_or_eq_of_le hi with h | h
    · exact hlt i h
    · subst h; exact htop
  have hmix : ∀ i j : ℕ, 1 ≤ i → i + j ≤ k →
      Work.Spaces.mixed j i (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
        = PsiInt F j z * sinProf i θ := by
    intro i j hi hij
    rw [hg, mixed_fstarSin_eq]
    congr 1
    exact hlt j (by omega)
  have hs0 : 0 ≤ Real.sin (2 * θ) := FstarHkOpen.sin_two_nonneg hθ
  have hγ1 : 1 ≤ Work.Spaces.gam α := le_of_lt (Work.Spaces.one_lt_gam hα)
  have hγ2 : Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have hpos2η : 0 ≤ (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := Real.rpow_nonneg hs0 _
  have hπ2 : (0 : ℝ) ≤ π / 2 := by positivity
  have hUj : ∀ i : ℕ, 0 ≤ FstarHkOpen.Uj F z i := fun i => FstarHkOpen.Uj_nonneg F z i
  have hle_K : ∀ i : ℕ, i ≤ k → FstarHkOpen.angK i ≤ FstarHkOpen.angKsum k := by
    intro i hi
    rw [FstarHkOpen.angKsum]
    exact Finset.single_le_sum (fun a _ => (FstarHkOpen.angK_pos a).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hCS : ∀ i ≤ k, (PsiInt F i z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ (π / 2) * FstarHkOpen.Uj F z i := fun i hi =>
    PsiInt_sq_mul_w_le_open F hF i hz
      (integrableOn_zSummand α k hF hmem i hi (Set.mem_Ici.mpr hz.le))
  rw [Work.Spaces.HkIntegrand]
  refine add_le_add ?_ ?_
  · calc ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i
            (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = ∑ i ∈ Finset.range (k + 1), (PsiInt F i z * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [hDz i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      _ = ∑ i ∈ Finset.range (k + 1), (PsiInt F i z) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          refine Finset.sum_congr rfl fun i _ => FstarHkOpen.zTerm_eq_on (PsiInt F i z) z θ hθ
      _ ≤ ∑ i ∈ Finset.range (k + 1), ((π / 2) * FstarHkOpen.Uj F z i)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_right
            (hCS i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) hpos2η
      _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
  · calc ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (Work.Spaces.mixed j i
              (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0)
        = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (PsiInt F j z * sinProf i θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, if_pos hc, hmix i j hc.1 hc.2]
          · rw [if_neg hc, if_neg hc]
      _ = ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2
              * ((sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
              else 0) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc, if_pos hc]
            exact FstarHkOpen.mixedTerm_eq_on α (PsiInt F j z) z (sinProf i) θ hθ
          · rw [if_neg hc, if_neg hc]
      _ ≤ ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            ((π / 2) * FstarHkOpen.Uj F z j * FstarHkOpen.angKsum k) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases hc : 1 ≤ i ∧ i + j ≤ k
          · rw [if_pos hc]
            have hi' : i ≤ k := by omega
            have hj' : j ≤ k := by omega
            have h1 : (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2
                * ((sinProf i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
                ≤ ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angK i :=
              mul_le_mul (hCS j hj')
                (FstarHkOpen.angK_bound i (Work.Spaces.gam α) hγ1 hγ2 hθ)
                (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))
                (mul_nonneg hπ2 (hUj j))
            have h2 : ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angK i
                ≤ ((π / 2) * FstarHkOpen.Uj F z j) * FstarHkOpen.angKsum k :=
              mul_le_mul_of_nonneg_left (hle_K i hi') (mul_nonneg hπ2 (hUj j))
            exact le_trans h1 h2
          · rw [if_neg hc]
            exact mul_nonneg (mul_nonneg hπ2 (hUj j)) (FstarHkOpen.angKsum_nonneg k)
      _ = (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * FstarHkOpen.angKsum k) := by
          have hrow : ∀ i : ℕ, (∑ j ∈ Finset.range (k + 1),
              ((π / 2) * FstarHkOpen.Uj F z j * FstarHkOpen.angKsum k))
              = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
                * FstarHkOpen.angKsum k := by
            intro i
            rw [← Finset.sum_mul, Finset.mul_sum]
          refine (Finset.sum_congr rfl (fun i _ => hrow i)).trans ?_
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring

set_option maxHeartbeats 3000000 in
/-- **The slice estimate.**  For almost every `z ∈ Iz`, the `θ`-integral of the `H^k`-integrand
of `F_*(F)·sin 2θ` is bounded by `hkConst k` times the `θ`-integral of the `H^k`-integrand
of `F`. -/
theorem slice_Hk_le_open (α : ℝ) (k : ℕ) (hF : SmoothOpen F)
    (hα : 0 < α) (hα1 : α ≤ 1) (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
        ≤ FstarHkOpen.hkConst k
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  have hmeas : (volume.restrict Work.Spaces.Iz) = volume.restrict (Set.Ioi 0) :=
    MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0)).symm
  rw [hmeas]
  have hae_le : ∀ {f g : ℝ → ℝ}, (∀ θ ∈ Work.Spaces.Iθ, f θ ≤ g θ) →
      f ≤ᵐ[volume.restrict Work.Spaces.Iθ] g := by
    intro f g h
    show ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ), f θ ≤ g θ
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    exact Eventually.of_forall h
  filter_upwards [HkIntegrand_fstarSin_le_open α k hF hα hα1 hmem,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz hzmem
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hzmem.le
  have hsumU : (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
    have hint : ∀ j ∈ Finset.range (k + 1), IntegrableOn (fun θ : ℝ =>
        (Work.Spaces.DzIter j F z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        Work.Spaces.Iθ :=
      fun j hj => integrableOn_zSummand α k hF hmem j
        (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hzI
    have hsum : (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        = ∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1), (Work.Spaces.DzIter j F z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      simp only [FstarHkOpen.Uj]
      rw [← MeasureTheory.integral_finsetSum]
      exact hint
    rw [hsum]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      (hmem.1 z hzI) (Eventually.of_forall fun θ => ?_)
    rw [Work.Spaces.HkIntegrand]
    exact le_add_of_nonneg_right (Work.Spaces.hkMixedSum_nonneg α k F z θ)
  have hcont1 : Continuous (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)) := by
    refine Continuous.mul continuous_const ?_
    refine Continuous.rpow (by fun_prop) continuous_const (fun θ => Or.inr ?_)
    rw [Work.Spaces.eta]; norm_num
  have hBc : (0 : ℝ) ≤ (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * FstarHkOpen.angKsum k) :=
    mul_nonneg (by positivity) (mul_nonneg
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => FstarHkOpen.Uj_nonneg F z j))
      (FstarHkOpen.angKsum_nonneg k))
  have hMint : IntegrableOn (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
      FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k)) Work.Spaces.Iθ :=
    (hcont1.add continuous_const).continuousOn.integrableOn_compact isCompact_Icc
  have hvol : volume.real Work.Spaces.Iθ = π / 2 := by
    rw [MeasureTheory.measureReal_def, Work.Spaces.Iθ, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  have hZa : ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) ≤ π / 2 := by
    have hle : ∀ θ ∈ Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) ≤ (1 : ℝ) :=
      fun θ hθ => Real.rpow_le_one (FstarHkOpen.sin_two_nonneg hθ)
        (FstarHkOpen.sin_two_le_one θ) (by rw [Work.Spaces.eta]; norm_num)
    calc ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) := by
          refine MeasureTheory.integral_mono_of_nonneg
            (hae_le fun θ hθ =>
              Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _)
            (integrableOn_const (s := Work.Spaces.Iθ) (C := (1 : ℝ))
              (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
            (hae_le hle)
      _ = π / 2 := FstarHkOpen.integral_Iθ_one
  have hZann : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta) := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    exact hae_le fun θ hθ => Real.rpow_nonneg (FstarHkOpen.sin_two_nonneg hθ) _
  have hIntM : ∫ θ in Work.Spaces.Iθ, ((π / 2) * (∑ j ∈ Finset.range (k + 1),
        FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
      + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k))
      = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2) := by
    have hInt1 : IntegrableOn (fun θ : ℝ => (π / 2) * (∑ j ∈ Finset.range (k + 1),
        FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact hcont1.continuousOn.integrableOn_compact isCompact_Icc
    have hInt2 : IntegrableOn (fun _ : ℝ => (k + 1) * ((π / 2)
        * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
        * FstarHkOpen.angKsum k)) Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]
      exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    rw [MeasureTheory.integral_add hInt1 hInt2]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const, smul_eq_mul, hvol]
    ring
  have hπ0 : (0 : ℝ) ≤ π / 2 := by positivity
  have hk0 : (0 : ℝ) ≤ (k + 1) := by positivity
  have hσ : 0 ≤ ∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j :=
    Finset.sum_nonneg fun j _ => FstarHkOpen.Uj_nonneg F z j
  have hK : 0 ≤ FstarHkOpen.angKsum k := FstarHkOpen.angKsum_nonneg k
  have hfin : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2)
      ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have h1 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2) :=
      mul_le_mul_of_nonneg_left hZa (mul_nonneg hπ0 hσ)
    have h2 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2)
          + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * FstarHkOpen.angKsum k) * (π / 2)
        ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
      have hAB : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k)
          ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
            * (1 + FstarHkOpen.angKsum k) := by
        have he : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k)
          = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (1 + (k + 1) * FstarHkOpen.angKsum k) := by ring
        rw [he]
        have hfac : 1 + (k + 1) * FstarHkOpen.angKsum k
            ≤ (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) := by
          nlinarith [hk0, hK, mul_nonneg hk0 hK]
        have hpos : (0 : ℝ) ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) :=
          mul_nonneg hπ0 hσ
        calc (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * (1 + (k + 1) * FstarHkOpen.angKsum k)
            = ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * (1 + (k + 1) * FstarHkOpen.angKsum k) := by ring
          _ ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j))
                * ((1 + (k + 1)) * (1 + FstarHkOpen.angKsum k)) :=
              mul_le_mul_of_nonneg_left hfac hpos
          _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
                * (1 + FstarHkOpen.angKsum k) := by ring
      have h3 : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
            * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) * (π / 2)
          ≤ FstarHkOpen.hkConst k * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by
        have heq : (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) * (π / 2)
            = ((π / 2) ^ 2 * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k))
              * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := by ring
        rw [heq, FstarHkOpen.hkConst]
        have hc0 : (0 : ℝ) ≤ (π / 2) ^ 2 * (1 + (k + 1)) * (1 + FstarHkOpen.angKsum k) :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith : (0:ℝ) ≤ 1 + (k + 1)))
            (by linarith : (0:ℝ) ≤ 1 + FstarHkOpen.angKsum k)
        nlinarith [hc0, hσ]
      calc (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (π / 2)
            + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              * FstarHkOpen.angKsum k) * (π / 2)
          = ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
              + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
                * FstarHkOpen.angKsum k)) * (π / 2) := by ring
        _ ≤ ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) * (1 + (k + 1))
              * (1 + FstarHkOpen.angKsum k)) * (π / 2) := mul_le_mul_of_nonneg_right hAB hπ0
        _ ≤ FstarHkOpen.hkConst k * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j) := h3
        _ ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
            mul_le_mul_of_nonneg_left hsumU (FstarHkOpen.hkConst_pos k).le
    linarith [h1, h2]
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
      ≤ ∫ θ in Work.Spaces.Iθ, ((π / 2) * (∑ j ∈ Finset.range (k + 1),
          FstarHkOpen.Uj F z j) * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta)
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k)) := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
          hMint (hae_le fun θ hθ => hz θ hθ)
    _ = (π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (2 - Work.Spaces.eta))
        + (k + 1) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), FstarHkOpen.Uj F z j)
          * FstarHkOpen.angKsum k) * (π / 2) := hIntM
    _ ≤ FstarHkOpen.hkConst k * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
        hfin

/-- **Lemma `HardyInequality4` for the angular moment** (Elgindi, §'Elliptic Regularity
Estimates'): for `0 < α ≤ 1` and `F` of class `C^∞` on the open quadrant with `F ∈ ℋ^k`, the
function `F_*(F)(z)·sin 2θ` is bounded in `ℋ^k` by a *universal* multiple (independent of `α`)
of `F`:

`|F_*(F)·sin 2θ|_{H^k} ≤ C_k |F|_{H^k}`. -/
theorem Fstar_Hk_le_open (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2))) →
      Work.Spaces.HkMem α k F →
      Work.Spaces.HkNorm α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  classical
  refine ⟨FstarHkOpen.hkConst k + 1,
    by linarith [FstarHkOpen.hkConst_pos k], ?_⟩
  intro α F hα hα1 hsm hmem
  have hF : SmoothOpen F := smoothOpen_of_forall hsm
  have hslice := slice_Hk_le_open α k hF hα hα1 hmem
  have hsq : Work.Spaces.HkSq α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ))
      ≤ (FstarHkOpen.hkConst k + 1) ^ 2 * Work.Spaces.HkSq α k F := by
    rw [Work.Spaces.HkSq, Work.Spaces.HkSq, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α k _ z θ)
      (hmem.2.const_mul ((FstarHkOpen.hkConst k + 1) ^ 2)) ?_
    filter_upwards [hslice] with z hz
    have h2 : 0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ :=
      integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
    have h3 : FstarHkOpen.hkConst k ≤ (FstarHkOpen.hkConst k + 1) ^ 2 := by
      nlinarith [FstarHkOpen.hkConst_pos k]
    exact le_trans hz (mul_le_mul_of_nonneg_right h3 h2)
  rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
  refine le_trans (Real.sqrt_le_sqrt hsq) (le_of_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by linarith [FstarHkOpen.hkConst_pos k])]

end Work.FTS.EllipticEst

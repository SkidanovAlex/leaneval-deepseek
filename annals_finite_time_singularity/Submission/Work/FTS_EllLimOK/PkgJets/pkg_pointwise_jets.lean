import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS_EllLimOK.Defs
import Submission.Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le
import Submission.Work.FTS_EllLimOK.VopTransfer.mixed_le_of_Vop_jets
import Submission.Work.FTS_EllLimOK.PkgJets.L12jets_classC
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.GalFields.RHS.SharpAux.Core
import Submission.Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## §1  the mixed jets of a separable product `A(z)·B(θ)` -/

private lemma sep_DthIter (i : ℕ) (A B : ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => A z * B θ)
      = fun z θ => A z * (Work.Spaces.Lop^[i] B) θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih]
      funext z θ
      show Real.sin (2 * θ) * deriv (fun θ' => A z * (Work.Spaces.Lop^[i] B) θ') θ
          = A z * (Work.Spaces.Lop^[i + 1] B) θ
      rw [deriv_const_mul_field (x := θ) (v := Work.Spaces.Lop^[i] B) (A z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

private lemma sep_DzIter (j : ℕ) (A C : ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A z * C θ)
      = fun z θ => (Work.Spaces.Zop^[j] A z) * C θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih]
      funext z θ
      show z * deriv (fun z' => Work.Spaces.Zop^[j] A z' * C θ) z
          = (Work.Spaces.Zop^[j + 1] A z) * C θ
      rw [deriv_mul_const_field (v := C θ) (u := Work.Spaces.Zop^[j] A) (x := z)]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Zop]
      ring

private lemma zop_eq_dziter (j : ℕ) (A : ℝ → ℝ) (z : ℝ) :
    Work.Spaces.Zop^[j] A z = Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  have h := congrFun (Work.Spaces.Zop_slice j (fun z _ => A z) 0) z
  exact h.symm

/-- The mixed jet of a separable product is the product of the `θ`-jet of `B` with the
`z`-jet of `A`. -/
private lemma mixed_sep (j i : ℕ) (A B : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => A z * B θ) z θ
      = (Work.Spaces.Lop^[i] B) θ * Work.Spaces.DzIter j (fun z _ => A z) z 0 := by
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => A z * B θ)) z θ = _
  rw [sep_DthIter i A B, sep_DzIter j A (Work.Spaces.Lop^[i] B)]
  show Work.Spaces.Zop^[j] A z * (Work.Spaces.Lop^[i] B) θ = _
  rw [zop_eq_dziter j A z]
  ring

/-- `D_θ^i` of a `(z,θ)`-function that only depends on `θ` is `Lop^i` of its `θ`-slice. -/
private lemma DthIter_sep_const (i : ℕ) (B : ℝ → ℝ) :
    ∀ z θ : ℝ, Work.Spaces.DthIter i (fun _ θ => B θ) z θ = (Work.Spaces.Lop^[i] B) θ := by
  induction i with
  | zero => intro z θ; rfl
  | succ i ih =>
      intro z θ
      rw [Work.Spaces.DthIter_succ]
      have hstep : Work.Spaces.DthIter i (fun _ θ => B θ) = fun _ θ => (Work.Spaces.Lop^[i] B) θ := by
        funext z θ
        exact ih z θ
      rw [hstep]
      show Real.sin (2 * θ) * deriv (fun θ' => (Work.Spaces.Lop^[i] B) θ') θ
          = (Work.Spaces.Lop^[i + 1] B) θ
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      try ring

private lemma DthIter_Sfun_eq (i : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter i Work.FTS.H2.Sfun z θ
      = (Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin (2 * θ))) θ :=
  DthIter_sep_const i (fun θ : ℝ => Real.sin (2 * θ)) z θ

/-! ## §2  the angular factors of `Θ` -/

/-- `Lop` commutes with multiplication by a constant. -/
private lemma Lop_const_mul (c : ℝ) : ∀ i : ℕ, ∀ B : ℝ → ℝ,
    Work.Spaces.Lop^[i] (fun θ => c * B θ) = fun θ => c * (Work.Spaces.Lop^[i] B) θ := by
  intro i
  induction i with
  | zero => intro B; rfl
  | succ i ih =>
      intro B
      rw [Function.iterate_succ_apply']
      rw [show Work.Spaces.Lop^[i] (fun θ => c * B θ) = fun θ => c * (Work.Spaces.Lop^[i] B) θ
        from ih B]
      funext θ
      show Real.sin (2 * θ) * deriv (fun θ' => c * (Work.Spaces.Lop^[i] B) θ') θ
          = c * (Work.Spaces.Lop^[i + 1] B) θ
      rw [deriv_const_mul_field (x := θ) (v := Work.Spaces.Lop^[i] B) c]
      rw [Function.iterate_succ_apply']
      simp only [Work.Spaces.Lop]
      ring

/-- `|D_θ^i (sin 2·)| ≤ Asin i` on the closed angular interval. -/
private lemma LopSin_bound (i : ℕ) (hi : i ≤ 4) (z : ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin (2 * θ))) θ| ≤ Work.FTS.H2.Asin i := by
  have h := Work.FTS.H2.abs_DthIter_Sfun_le i hi z hθ
  rw [DthIter_Sfun_eq i z θ] at h
  calc |(Work.Spaces.Lop^[i] (fun θ : ℝ => Real.sin (2 * θ))) θ|
      ≤ Work.FTS.H2.Asin i * Real.sin (2 * θ) := h
    _ ≤ Work.FTS.H2.Asin i * 1 :=
        mul_le_mul_of_nonneg_left (Real.sin_le_one _) (Work.FTS.H2.Asin_pos i).le
    _ = Work.FTS.H2.Asin i := mul_one _

private lemma Asin_le_384 (i : ℕ) (hi : i ≤ 4) : Work.FTS.H2.Asin i ≤ 384 := by
  interval_cases i <;> norm_num [Work.FTS.H2.Asin]

private lemma LopScaled_bound {α : ℝ} (hα : 0 < α) (i : ℕ) (hi : i ≤ 4) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |(Work.Spaces.Lop^[i] (fun θ : ℝ => (1 / (4 * α)) * Real.sin (2 * θ))) θ|
      ≤ (1 / (4 * α)) * Work.FTS.H2.Asin i := by
  rw [Lop_const_mul (1 / (4 * α)) i (fun θ : ℝ => Real.sin (2 * θ))]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (4 * α))]
  exact mul_le_mul_of_nonneg_left (LopSin_bound i hi (0 : ℝ) hθ) (by positivity)

/-! ## §3  the mixed jets of `Θ α g` -/

/-- `Θ α g` is the separable product `B(θ)·A(z)`, `B θ = (1/(4α)) sin 2θ`,
`A z = L₁₂ g z`, so its mixed jets factor. -/
private lemma Theta_mixed_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ
      = (Work.Spaces.Lop^[i] (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))) θ
        * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0 := by
  have hfun : Work.Construction.Theta α g
      = (fun z θ => Work.Construction.L12 g z * ((1 / (4 * α)) * Real.sin (2 * θ))) := by
    funext z θ
    simp only [Work.Construction.Theta, Work.Construction.s2]
    ring
  rw [hfun]
  exact mixed_sep j i (fun z => Work.Construction.L12 g z)
    (fun θ => (1 / (4 * α)) * Real.sin (2 * θ)) z θ

/-- **The mixed jets of `Θ α g` are bounded by the `D_z`-jets of `L₁₂ g`.** -/
private lemma Theta_jets_aux {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ → ℝ} {CL : ℝ} (hCL0 : 0 ≤ CL)
    (hL12 : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
        ≤ CL * Work.FTS.StrongGlobal.Xn6 α g) :
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Theta α g) z θ|
        ≤ ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α g) := by
  intro j i hji z θ hz hθ0 hθ2
  have hj4 : j ≤ 4 := by omega
  have hi4 : i ≤ 4 := by omega
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ0.le, hθ2.le⟩
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  rw [Theta_mixed_eq α g j i z θ]
  have hLop := LopScaled_bound hα i hi4 hθIθ
  have hDz := hL12 j hj4 z hz
  calc |(Work.Spaces.Lop^[i] (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))) θ
          * Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
      = |(Work.Spaces.Lop^[i] (fun θ => (1 / (4 * α)) * Real.sin (2 * θ))) θ|
        * |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0| := abs_mul _ _
    _ ≤ ((1 / (4 * α)) * Work.FTS.H2.Asin i) * (CL * Work.FTS.StrongGlobal.Xn6 α g) :=
        mul_le_mul hLop hDz (abs_nonneg _)
          (mul_nonneg (by positivity) (Work.FTS.H2.Asin_pos i).le)
    _ ≤ ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α g) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCL0 hXnn)
        exact mul_le_mul_of_nonneg_left (Asin_le_384 i hi4) (by positivity)

/-- `Θ α g` is `C^∞` on the open quadrant for a Galerkin-elliptic package. -/
private lemma Theta_smoothOpen {α Ce : ℝ} (hα : 0 < α) {g Φg : ℝ → ℝ → ℝ}
    (hGo : Work.FTS.VocabO.EllPkgGo α Ce g Φg) :
    Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α g) := by
  have hEq : Work.Construction.Theta α g
      = (fun z θ => (1 / (4 * α)) * Real.sin (2 * θ) * Work.Construction.L12 g z) := by
    funext z θ
    simp only [Work.Construction.Theta, Work.Construction.s2]
  rw [hEq]
  exact Work.FTS.NonlinRows.NRow10aux.smoothOpen_mul
    (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
      Work.FTS.GalFields.RHS.smoothOpen_sin_two)
    (Work.FTS.GalFields.RHS.Sharp.smoothOpen_L12_gal hα hGo)

/-! ## §4  the assembly -/

/-- **The assembly**, parameterised by the `D_z`-jet bound for `L₁₂ g` on the class `C`. -/
private theorem pkg_pointwise_jets_aux {α Ce CL : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hCL0 : 0 ≤ CL)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : HasPkg α Ce E) {fn : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hL : LimSeq4 α fn f)
    (hpin : ∀ n : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α (fn n) (E (fn n)) z s) (𝓝[<] (π / 2)) (𝓝 0))
    (hL12j : ∀ (g : Work.FTS.Galerkin.Fn), Work.FTS.ClassC.ClassC α g →
      ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
        |Work.Spaces.DzIter j (fun z _ => Work.Construction.L12 g z) z 0|
          ≤ CL * Work.FTS.StrongGlobal.Xn6 α g) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C := by
  obtain ⟨CS, hCS0, hCS⟩ := Work.FTS_EllLimOK.SlotSup.slot_jets_sup_le α hα hα1
  obtain ⟨CV, hCV0, hCV⟩ := Work.FTS_EllLimOK.VopTransfer.mixed_le_of_Vop_jets
  obtain ⟨B, hB⟩ := hL.bound
  have hB0 : (0 : ℝ) ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 6 (fn 0)) (hB 0)
  refine ⟨CV * (CS * (|Ce| * B)) + ((1 / (4 * α)) * 384) * (CL * B) + 1, by positivity, ?_⟩
  intro n j i hji z θ hzθ
  have hz : 0 < z := hzθ.1
  have hθI : θ ∈ Set.Ioo (0 : ℝ) (π / 2) := hzθ.2
  have hθ0 : 0 < θ := hzθ.2.1
  have hθ2 : θ < π / 2 := hzθ.2.2
  -- the two packages at `fn n`
  have hPkg := hE (fn n) (hL.classC n)
  have hGo : Work.FTS.VocabO.EllPkgGo α Ce (fn n) (E (fn n)) := hPkg.1
  have hK : Work.FTS.ClassC.EllPkgK α 6 Ce (fn n) (E (fn n)) := hPkg.2
  -- smoothness of `Φ̃` and of `Θ`
  have hΦsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.PhiTil α (fn n) (E (fn n))) :=
    Work.FTS.GalFields.RHS.Sharp.smoothOpen_PhiTil hα hGo
  have hΘsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Theta α (fn n)) :=
    Theta_smoothOpen hα hGo
  have hXnn : 0 ≤ Work.FTS.StrongGlobal.Xn6 α (fn n) :=
    Work.Spaces.HkNorm_nonneg α 6 (fn n)
  have hφnn : 0 ≤ |Ce| * B := mul_nonneg (abs_nonneg Ce) hB0
  -- ## the jets of `Vop Φ̃`, from the package and the `ℋ⁶`-slot bound
  have hVjets : ∀ j l : ℕ, j + l ≤ 4 → ∀ z' θ' : ℝ, 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j l (Work.Construction.Vop
        (Work.Construction.PhiTil α (fn n) (E (fn n)))) z' θ'| ≤ CS * (|Ce| * B) := by
    intro j l hjl z' θ' hz' hθ'
    refine le_trans (hCS _ hK.V.1.1 hK.V.1.2 j l (by omega) z' θ' hz' hθ'.1 hθ'.2) ?_
    refine mul_le_mul_of_nonneg_left ?_ hCS0.le
    calc Work.Spaces.HkNorm α 6 (Work.Construction.Vop
            (Work.Construction.PhiTil α (fn n) (E (fn n))))
        ≤ Ce * Work.Spaces.HkNorm α 6 (fn n) := hK.V.2
      _ ≤ |Ce| * Work.Spaces.HkNorm α 6 (fn n) :=
          mul_le_mul_of_nonneg_right (le_abs_self Ce)
            (Work.Spaces.HkNorm_nonneg α 6 (fn n))
      _ ≤ |Ce| * B := mul_le_mul_of_nonneg_left (hB n) (abs_nonneg Ce)
  -- ## the jets of `Φ̃`
  have hΦjets : ∀ j i : ℕ, j + i ≤ 4 → ∀ z' θ' : ℝ, 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j i (Work.Construction.PhiTil α (fn n) (E (fn n))) z' θ'|
        ≤ CV * (CS * (|Ce| * B)) :=
    hCV (CS * (|Ce| * B)) (mul_nonneg hCS0.le hφnn) _
      hΦsm (hpin n) hVjets
  -- ## the jets of `Θ α (fn n)`
  have hΘjets : ∀ j i : ℕ, j + i ≤ 4 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (Work.Construction.Theta α (fn n)) z' θ'|
        ≤ ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α (fn n)) :=
    Theta_jets_aux hα hCL0 (hL12j (fn n) (hL.classC n))
  -- ## the decomposition `E (fn n) = Φ̃ + Θ`
  have hdec : E (fn n) = fun z θ => Work.Construction.PhiTil α (fn n) (E (fn n)) z θ
      + Work.Construction.Theta α (fn n) z θ := by
    funext z' θ'
    simp only [Work.Construction.PhiTil]
    ring
  rw [hdec, Work.FTS.EllipticEst.SmoothOpen.mixed_add hΦsm hΘsm j i z θ hz hθ0 hθ2]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (hΦjets j i hji z θ hz hθI)
    (hΘjets j i hji z θ hz hθ0 hθ2)) ?_
  have hle : ((1 / (4 * α)) * 384) * (CL * Work.FTS.StrongGlobal.Xn6 α (fn n))
      ≤ ((1 / (4 * α)) * 384) * (CL * B) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hB n) hCL0) (by positivity)
  linarith

theorem pkg_pointwise_jets {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.HasPkg α Ce E) {fn : ℕ → Work.FTS.Galerkin.Fn}
    {f : Work.FTS.Galerkin.Fn} (hL : Work.FTS_EllLimOK.LimSeq4 α fn f)
    (hpin : ∀ n : ℕ, ∀ z ∈ Set.Ioi (0 : ℝ),
      Filter.Tendsto (fun s => Real.cos s
        * Work.Construction.PhiTil α (fn n) (E (fn n)) z s) (𝓝[<] (π / 2)) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.mixed j i (E (fn n)) z θ| ≤ C := by
  obtain ⟨CL, hCL0, hCL⟩ := L12jets_classC hα hα1
  exact pkg_pointwise_jets_aux hα hα1 hCL0.le hE hL hpin hCL

end Work.FTS_EllLimOK.PkgJets

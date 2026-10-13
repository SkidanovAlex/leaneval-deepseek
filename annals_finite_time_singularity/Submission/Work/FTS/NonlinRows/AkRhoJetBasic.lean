import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.IntervalCases
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace Work.FTS.NonlinRows.AkRhoJetBasic

/-! ## The radial jet bound for `2z^2/(1+z)^3`

Extracted from `Work.FTS.Nonlinear.Pieces` (where it is `private`) as the standalone
input of the `rak` row: the `D_z^j`-jets (`j <= 4`) of `2z^2/(1+z)^3` weighted by the
Hardy weight `w z = (1+z)^2/z^2` are bounded by `720/(1+z)`. -/

/-- The `j`-th `D_z`-jet of `2z²/(1+z)³` weighted by the Hardy weight `w`. -/
noncomputable def akRho (j : ℕ) (z : ℝ) : ℝ :=
  match j with
  | 0 => 2 / (1 + z)
  | 1 => 2 * (2 - z) / (1 + z) ^ 2
  | 2 => 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 3
  | 3 => 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 4
  | _ => (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 5

def akNum : ℕ → ℕ → ℝ
  | 0, i => if i = 0 then 2 else 0
  | 1, i => if i = 0 then 4 else if i = 1 then -2 else 0
  | 2, i => if i = 0 then 8 else if i = 1 then -14 else if i = 2 then 2 else 0
  | 3, i => if i = 0 then 16 else if i = 1 then -66 else if i = 2 then 36
              else if i = 3 then -2 else 0
  | _, i => if i = 0 then 32 else if i = 1 then -262 else if i = 2 then 342
              else if i = 3 then -82 else if i = 4 then 2 else 0

lemma akRho_eq (j : ℕ) (hj : j ≤ 4) (z : ℝ) :
    akRho j z = (∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i) / (1 + z) ^ (j + 1) := by
  interval_cases j <;>
    · simp only [akRho, akNum]
      norm_num [Finset.sum_range_succ]
      try ring

lemma akNum_sum_le (j : ℕ) (hj : j ≤ 4) :
    (∑ i ∈ Finset.range (j + 1), |akNum j i|) ≤ 720 := by
  interval_cases j <;> simp [akNum, Finset.sum_range_succ] <;> norm_num

lemma akRho_abs_le (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 ≤ z) :
    |akRho j z| ≤ 720 / (1 + z) := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h1' : (1 : ℝ) ≤ 1 + z := by linarith
  have hsum : |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i| ≤ 720 * (1 + z) ^ j := by
    calc |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i|
        ≤ ∑ i ∈ Finset.range (j + 1), |akNum j i * z ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (j + 1), |akNum j i| * (1 + z) ^ j := by
          refine Finset.sum_le_sum (fun i hi => ?_)
          rw [Finset.mem_range] at hi
          have h2 : |z| ^ i ≤ (1 + z) ^ i := by
            refine pow_le_pow_left₀ (abs_nonneg z) ?_ i
            rw [abs_of_nonneg hz]; linarith
          have h3 : (1 + z) ^ i ≤ (1 + z) ^ j := pow_le_pow_right₀ h1' (by omega)
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left (le_trans h2 h3) (abs_nonneg _)
      _ = (∑ i ∈ Finset.range (j + 1), |akNum j i|) * (1 + z) ^ j := by rw [Finset.sum_mul]
      _ ≤ 720 * (1 + z) ^ j := mul_le_mul_of_nonneg_right (akNum_sum_le j hj) (by positivity)
  rw [akRho_eq j hj z, abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + z) ^ (j + 1))]
  rw [div_le_div_iff₀ (by positivity) h1]
  calc |∑ i ∈ Finset.range (j + 1), akNum j i * z ^ i| * (1 + z)
      ≤ (720 * (1 + z) ^ j) * (1 + z) := mul_le_mul_of_nonneg_right hsum h1.le
    _ = 720 * (1 + z) ^ (j + 1) := by rw [mul_assoc, ← pow_succ]

lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) (n * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z
    ((hasDerivAt_const (x := z) 1).add (hasDerivAt_id z))
  simpa [Function.comp_def] using h

lemma hasDerivAt_akPsi {z : ℝ} (hz : z ≠ -1) :
    HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3)
      (2 * z * (2 - z) / (1 + z) ^ 4) z := by
  have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2) (4 * z) z := by
    have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
    convert h using 1
    push_cast
    ring
  have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 3) (3 * (1 + z) ^ 2) z := by
    simpa using hasDerivAt_one_add_pow 3 z
  have h3 : (1 + z) ^ 3 ≠ 0 :=
    pow_ne_zero 3 (by intro hc; exact hz (by linarith))
  have hd := h1.div h2 h3
  convert hd using 1
  field_simp <;> ring_nf <;> norm_num

lemma akJet1 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 1 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (2 - z) / (1 + z) ^ 4 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz]
  have h : (fun z' : ℝ => (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3 : ℝ → ℝ → ℝ) z' θ)
      = fun z' : ℝ => 2 * z' ^ 2 / (1 + z') ^ 3 := rfl
  rw [h, (hasDerivAt_akPsi hz).deriv]
  ring

lemma akJet2 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 2 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (z ^ 2 - 7 * z + 4) / (1 + z) ^ 5 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 1 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (2 - z') / (1 + z') ^ 4 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet1 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (2 - z') / (1 + z') ^ 4)
      (2 * z * (4 - 7 * z + z ^ 2) / (1 + z) ^ 5) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (2 - z')) (2 * z * (4 - 3 * z)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h' := h.mul ((hasDerivAt_const (x := z) (c := (2 : ℝ))).sub (hasDerivAt_id z))
      convert h' using 1
      · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 4) (4 * (1 + z) ^ 3) z := by
      simpa using hasDerivAt_one_add_pow 4 z
    have h3 : (1 + z) ^ 4 ≠ 0 :=
      pow_ne_zero 4 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

lemma akJet3 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 3 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = 2 * z ^ 2 * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 2 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4) / (1 + z') ^ 5 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet2 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4) / (1 + z') ^ 5)
      (2 * z * (-z ^ 3 + 18 * z ^ 2 - 33 * z + 8) / (1 + z) ^ 6) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (z' ^ 2 - 7 * z' + 4))
        (2 * z * (8 - 21 * z + 4 * z ^ 2)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun z' : ℝ => z' ^ 2 - 7 * z' + 4) (2 * z - 7) z := by
        have a := (hasDerivAt_pow 2 z)
        have b := (hasDerivAt_id z).const_mul (7 : ℝ)
        have c := (a.sub b).add_const 4
        convert c using 1
        · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
        · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
      have h' := h.mul h2
      convert h' using 1
      simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      ; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 5) (5 * (1 + z) ^ 4) z := by
      simpa using hasDerivAt_one_add_pow 5 z
    have h3 : (1 + z) ^ 5 ≠ 0 :=
      pow_ne_zero 5 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

lemma akJet4 {z : ℝ} (hz : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter 4 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ
      = z ^ 2 * (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 7 := by
  rw [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
  have hev : (fun z' : ℝ => Work.Spaces.DzIter 3 (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z' θ)
      =ᶠ[𝓝 z] fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8) / (1 + z') ^ 6 := by
    filter_upwards [isOpen_ne.mem_nhds hz] with z' hz'
    exact akJet3 hz' θ
  rw [hev.deriv_eq]
  have hd : HasDerivAt
      (fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8) / (1 + z') ^ 6)
      (z * (2 * z ^ 4 - 82 * z ^ 3 + 342 * z ^ 2 - 262 * z + 32) / (1 + z) ^ 7) z := by
    have h1 : HasDerivAt (fun z' : ℝ => 2 * z' ^ 2 * (-z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8))
        (2 * z * (-5 * z ^ 3 + 72 * z ^ 2 - 99 * z + 16)) z := by
      have h := (hasDerivAt_pow 2 z).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun z' : ℝ => -z' ^ 3 + 18 * z' ^ 2 - 33 * z' + 8)
          (-3 * z ^ 2 + 36 * z - 33) z := by
        have a := (hasDerivAt_pow 3 z).neg
        have b := (hasDerivAt_pow 2 z).const_mul (18 : ℝ)
        have c := (hasDerivAt_id z).const_mul (33 : ℝ)
        have h' := ((a.add b).sub c).add_const 8
        convert h' using 1
        · funext z'; simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
        · simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]; push_cast; ring
      have h' := h.mul h2
      convert h' using 1
      simp only [Nat.reduceSub, Nat.cast_ofNat, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Function.const_apply, id_eq]
      ; push_cast; ring
    have h2 : HasDerivAt (fun z' : ℝ => (1 + z') ^ 6) (6 * (1 + z) ^ 5) z := by
      simpa using hasDerivAt_one_add_pow 6 z
    have h3 : (1 + z) ^ 6 ≠ 0 :=
      pow_ne_zero 6 (by intro hc; exact hz (by linarith))
    have hd := h1.div h2 h3
    convert hd using 1
    field_simp <;> ring_nf <;> norm_num
  rw [hd.deriv]
  ring

lemma akJet_mul_w (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz0 : z ≠ 0) (hz1 : z ≠ -1) (θ : ℝ) :
    Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z
      = akRho j z := by
  have h1z : (1 : ℝ) + z ≠ 0 := by intro hc; exact hz1 (by linarith)
  interval_cases j
  · simp only [akRho, Work.Spaces.DzIter_zero]
    rw [Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet1 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet2 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet3 hz1 θ, akRho, Work.Spaces.w]
    field_simp <;> ring_nf <;> norm_num
  · rw [akJet4 hz1 θ, akRho, Work.Spaces.w] <;> try norm_num
    field_simp <;> ring_nf <;> norm_num

lemma akJet_bound (j : ℕ) (hj : j ≤ 4) {z : ℝ} (hz : 0 < z) (θ : ℝ) :
    (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
      ≤ 720 ^ 2 / (1 + z) ^ 2 := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hz1 : z ≠ -1 := by intro hc; linarith
  rw [akJet_mul_w j hj hz0 hz1 θ]
  have h := akRho_abs_le j hj hz.le
  have h2 : akRho j z ^ 2 ≤ (720 / (1 + z)) ^ 2 := by
    have h3 := pow_le_pow_left₀ (abs_nonneg (akRho j z)) h 2
    rwa [sq_abs] at h3
  calc akRho j z ^ 2 ≤ (720 / (1 + z)) ^ 2 := h2
    _ = 720 ^ 2 / (1 + z) ^ 2 := by rw [div_pow]

/-- **The radial jet bound** for the profile `z ↦ 2z^2/(1+z)^3` (the radial factor of
`AK α`), in the form needed by `Work.FTS.LocDataExt.HkIntegrand_sepGam_le`. -/
theorem akRho_jet_bound :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ j : ℕ, j ≤ 4 → ∀ {z : ℝ}, 0 < z → ∀ θ : ℝ,
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2 :=
  ⟨720 ^ 2, by norm_num, fun j hj z hz θ => akJet_bound j hj hz θ⟩

end Work.FTS.NonlinRows.AkRhoJetBasic

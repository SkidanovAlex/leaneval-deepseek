/-
# `HkAdm` is preserved by `D_θ` and `D_z` (one order down)

`HkAdm α k f` is the admissible class of the `ℋ^k`-coercivity layer: `f` smooth on a
neighbourhood of the closed quadrant, every mixed `D`-derivative `D_z^b D_θ^a f` with
`a + b ≤ k` lying in `ℋ^k`, and its `L₁₂`-zero-mode `L₁₂(D_z^bD_θ^a f)(0)` vanishing.

The two claims of this file are the closure properties used by the induction:

* `HkAdm α (k+1) f → HkAdm α k (D_θ f)`:  since `D_θ^i(D_θ f) = D_θ^{i+1} f` as
  functions, every mixed derivative of `D_θ f` of total order `≤ k` *is* a mixed
  derivative of `f` of total order `≤ k+1`, and `HkMem` descends by one order
  (`HkMem_mono`);
* `HkAdm α (k+1) f → HkAdm α k (D_z f)`:  here `D_z` and `D_θ` do not commute as
  *functions*, but they do commute on the open set of `SmoothNbhd`
  (`Spaces.mixed_comm`), so `D_z^b D_θ^a(D_z f) = D_z^{b+1} D_θ^a f` on the quadrant;
  the membership and the `L₁₂`-condition transfer because both `HkMem` and `L₁₂(·)(0)`
  only see the values (and germs) of the function on `(0,∞) × [0,π/2]`
  (`HkMem_congr_of_eqOn_Ioi`, `L12f_eq_of_eqOn_Ioi_Iθ`).
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.HkMem_mono
import Submission.Work.Coercivity.CommutZ_HkIntegrand_congr_pt
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FM.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## `L₁₂(f)(0)` only depends on the values of `f` on the quadrant -/

/-- The value `L₁₂(f)(0) = ∫_{(0,∞)} ∫_{Iθ} K(θ) f(s,θ)/s` depends only on the values
of `f` on `(0,∞) × Iθ`, the domain of the iterated integral. -/
theorem L12f_eq_of_eqOn_Ioi_Iθ {u v : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ, u z θ = v z θ) :
    L12f u 0 = L12f v 0 := by
  simp only [L12f, FM.L12, FM.L12dens]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
  rw [h s hs θ hθ]

/-- `H^k`-membership only depends on the values of the function on `(0,∞) × Iθ`: the
`H^k`-integrand is a local functional of the iterated derivatives, so it agrees at every
interior point of the quadrant, and on the null slice `z = 0` it vanishes identically
for every function. -/
theorem HkMem_congr_of_eqOn_Ioi (α : ℝ) (k : ℕ) {u v : ℝ → ℝ → ℝ}
    (hu : Spaces.HkMem α k u)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ, u z θ = v z θ) :
    Spaces.HkMem α k v := by
  -- interior points of the quadrant: the integrands agree (local functional, `u = v`)
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Spaces.HkIntegrand α k u z θ = Spaces.HkIntegrand α k v z θ :=
    CommutZ_HkIntegrand_congr_pt α k u v h
  -- hence the `θ`-slices agree a.e. on `Iθ` (the two endpoints of `Iθ` are null)
  have hslice_eq : ∀ z ∈ Spaces.Iz,
      (fun θ => Spaces.HkIntegrand α k u z θ) =ᵐ[volume.restrict Spaces.Iθ]
        (fun θ => Spaces.HkIntegrand α k v z θ) := by
    intro z hz
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hz0
    · -- at `z = 0` both integrands vanish identically
      rw [← hz0]
      filter_upwards with θ
      simp only [Spaces.HkIntegrand_zero_z]
    · have hmeas : volume.restrict Spaces.Iθ
          = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) :=
        (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc).symm
      rw [hmeas]
      refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      exact hpt z hz0 θ hθ
  constructor
  · intro z hz
    exact Integrable.congr (hu.1 z hz) (hslice_eq z hz)
  · refine Integrable.congr hu.2 ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact MeasureTheory.integral_congr_ae (hslice_eq z hz)

/-! ## The operator identities -/

/-- `D_θ^i (D_θ f) = D_θ^{i+1} f`, as functions. -/
theorem DthIter_Dth_eq (f : ℝ → ℝ → ℝ) (i : ℕ) :
    Spaces.DthIter i (Spaces.Dth f) = Spaces.DthIter (i + 1) f :=
  Spaces.DthIter_add_right i 1 f

/-- `D_z^b D_θ^a (D_θ f) = D_z^b D_θ^{a+1} f`, as functions. -/
theorem mixed_Dth_eq (f : ℝ → ℝ → ℝ) (b a : ℕ) :
    Spaces.mixed b a (Spaces.Dth f) = Spaces.mixed b (a + 1) f := by
  simp only [Spaces.mixed]
  rw [DthIter_Dth_eq]

/-- On the quadrant, `D_z^b D_θ^a (D_z f) = D_z^{b+1} D_θ^a f`: the operators `D_z` and
`D_θ` commute on the open set of `SmoothNbhd` (`Spaces.mixed_comm`).  Note that this is
an identity on the quadrant only; the two functions differ in general off it. -/
theorem mixed_Dz_eq {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) (b a : ℕ) {z θ : ℝ}
    (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed b a (Spaces.Dz f) z θ = Spaces.mixed (b + 1) a f z θ := by
  have h := Spaces.mixed_comm f hf b a 1 0 z θ hz hθ
  simpa only [Spaces.mixed_zero_right, Spaces.DzIter_succ, Spaces.DzIter_zero,
    Nat.add_zero] using h

/-- The same identity, with the `z ∈ Iz` hypothesis in the form `0 < z`. -/
theorem mixed_Dz_eq_of_pos {f : ℝ → ℝ → ℝ} (hf : Spaces.SmoothNbhd f) (b a : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Spaces.Iθ) :
    Spaces.mixed b a (Spaces.Dz f) z θ = Spaces.mixed (b + 1) a f z θ :=
  mixed_Dz_eq hf b a (Set.mem_Ici.mpr (le_of_lt hz)) hθ

/-! ## The closure of `HkAdm` under `D_θ` and `D_z` -/

theorem HkAdm_dth (α : ℝ) (k : ℕ) {f : ℝ → ℝ → ℝ} (h : HkAdm α (k + 1) f) :
    HkAdm α k (Spaces.Dth f) ∧ HkAdm α k (Spaces.Dz f) := by
  obtain ⟨hsm, hmem, hL12⟩ := h
  constructor
  · -- ## `D_θ`
    refine ⟨Spaces.SmoothNbhd.Dth hsm, ?_, ?_⟩
    · intro a b hab
      rw [mixed_Dth_eq f b a]
      exact HkMem_mono α k (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsm (a + 1)) b)
        (hmem (a + 1) b (by omega))
    · intro a b hab
      rw [mixed_Dth_eq f b a]
      exact hL12 (a + 1) b (by omega)
  · -- ## `D_z`
    refine ⟨Spaces.SmoothNbhd.Dz hsm, ?_, ?_⟩
    · intro a b hab
      have heq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ,
          Spaces.mixed (b + 1) a f z θ = Spaces.mixed b a (Spaces.Dz f) z θ :=
        fun z hz θ hθ => (mixed_Dz_eq_of_pos hsm b a hz hθ).symm
      exact HkMem_congr_of_eqOn_Ioi α k
        (HkMem_mono α k (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsm a) (b + 1))
          (hmem a (b + 1) (by omega))) heq
    · intro a b hab
      have heq : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Spaces.Iθ,
          Spaces.mixed b a (Spaces.Dz f) z θ = Spaces.mixed (b + 1) a f z θ :=
        fun z hz θ hθ => mixed_Dz_eq_of_pos hsm b a hz hθ
      rw [L12f_eq_of_eqOn_Ioi_Iθ heq]
      exact hL12 a (b + 1) (by omega)

end Work.Coercivity

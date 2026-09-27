import Mathlib
import Submission.Work.Mostow.ParabolicDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.BusemannLipschitz
import Submission.Work.Mostow.ParabolicBusemannLip
import Submission.Work.Mostow.geomFiniteStabHorosphere

/-!
# `geomFiniteParabolicClass`

A parabolic isometry `g ∈ PO(n,1)` (no fixed point in `ℍⁿ`, infimal displacement `0`) has

* a fixed point `ξ` on the boundary sphere `Sph n`,
* exactly one such fixed point,
* and it preserves every horoball based at `ξ` (equivalently `busemann ξ (g·u) = busemann ξ u`).

The proof is the standard one, done in the chart `E n = ℍⁿ` of `Interfaces.lean`:

* a minimising sequence `u_k` of `u ↦ hdist u (g·u)` is unbounded, and its normalised points
  `(tpart u_k)⁻¹ • u_k` have a subsequence converging to a boundary point `ξ`;
* writing `ζ = bd g ξ` and `c = busemann ζ (g·0)`, the Busemann cocycle gives
  `busemann ζ (g·u) = busemann ξ u + c`, while `busemann ζ` is `1`-Lipschitz, so along the
  minimising sequence `busemann ξ u_k - busemann ζ u_k` tends both to the finite number `-c` and
  (when `ζ ≠ ξ`) to `-∞`; hence `ζ = ξ`;
* if `ξ ≠ η` were both fixed then `bCocy g ξ = bCocy g η = 0`, so the orbit of `0` lies in the
  bounded set `{busemann ξ = 0} ∩ {busemann η = 0}`; a bounded orbit has a fixed point (proved
  below via the projective mean in the hyperboloid model), contradicting parabolicity.
-/

set_option maxHeartbeats 8000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter

noncomputable section

variable {n : ℕ}

/-! ## Elementary facts about the chart -/

theorem parab_norm_lt_tpart (u : E n) : ‖u‖ < tpart u := by
  have h : Real.sqrt (‖u‖ ^ 2) < Real.sqrt (1 + ‖u‖ ^ 2) :=
    Real.sqrt_lt_sqrt (sq_nonneg ‖u‖) (by linarith [sq_nonneg ‖u‖])
  rwa [Real.sqrt_sq (norm_nonneg u)] at h

theorem parab_norm_smul_tpart_inv (u : E n) :
    ‖(tpart u)⁻¹ • u‖ = ‖u‖ / tpart u := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (tpart_pos u), div_eq_inv_mul]

theorem parab_norm_smul_tpart_inv_lt_one (u : E n) : ‖(tpart u)⁻¹ • u‖ < 1 := by
  rw [parab_norm_smul_tpart_inv, div_lt_one (tpart_pos u)]
  exact parab_norm_lt_tpart u

theorem parab_norm_le_of_le_mul_tpart {u : E n} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ‖u‖ ≤ r * tpart u) : ‖u‖ ≤ r / Real.sqrt (1 - r ^ 2) := by
  have h1 : 0 < 1 - r ^ 2 := by nlinarith
  have ht : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := Real.sq_sqrt (by positivity)
  have h2 : ‖u‖ ^ 2 ≤ r ^ 2 * (1 + ‖u‖ ^ 2) := by
    have h3 : ‖u‖ ^ 2 ≤ (r * tpart u) ^ 2 := pow_le_pow_left₀ (norm_nonneg u) h 2
    rwa [mul_pow, ht] at h3
  have h4 : ‖u‖ ^ 2 * (1 - r ^ 2) ≤ r ^ 2 := by nlinarith [h2]
  have h5 : ‖u‖ ^ 2 ≤ r ^ 2 / (1 - r ^ 2) := by
    rw [le_div_iff₀ h1]; linarith [h4]
  calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ Real.sqrt (r ^ 2 / (1 - r ^ 2)) := Real.sqrt_le_sqrt h5
    _ = r / Real.sqrt (1 - r ^ 2) := by
        rw [Real.sqrt_div (sq_nonneg r), Real.sqrt_sq hr0]

theorem parab_inner_sinh_smul {ξ : E n} (hξ : ‖ξ‖ = 1) (t : ℝ) :
    inner ℝ (Real.sinh t • ξ) ξ = Real.sinh t := by
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq, hξ]
  ring

theorem parab_sphere_norm {ξ : E n} (hξ : ξ ∈ Sph n) : ‖ξ‖ = 1 := (mem_Sph_iff ξ).mp hξ

theorem parab_busemann_ray_self {ξ : E n} (hξ : ξ ∈ Sph n) (t : ℝ) :
    busemann ξ (Real.sinh t • ξ) = -t := by
  have hξn : ‖ξ‖ = 1 := parab_sphere_norm hξ
  rw [busemann, tpart_sinh_smul ξ t hξn, parab_inner_sinh_smul hξn]
  have h : Real.cosh t - Real.sinh t = Real.exp (-t) := by
    rw [Real.cosh_eq, Real.sinh_eq]; ring
  rw [h, Real.log_exp]

/-- The two horospheres `{busemann ξ = 0}` and `{busemann η = 0}` for `ξ ≠ η` meet in a
bounded set. -/
theorem parab_exists_norm_bound {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hne : ξ ≠ η) :
    ∃ R : ℝ, ∀ u : E n, busemann ξ u = 0 → busemann η u = 0 → ‖u‖ ≤ R := by
  have hξn : ‖ξ‖ = 1 := parab_sphere_norm hξ
  have hηn : ‖η‖ = 1 := parab_sphere_norm hη
  set ρ : ℝ := 1 - inner ℝ ξ η with hρdef
  have hρ : 0 < ρ := by
    have hpos : 0 < ‖ξ - η‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    have h : 0 < ‖ξ - η‖ ^ 2 := pow_pos hpos 2
    rw [norm_sub_sq_real, hξn, hηn] at h
    rw [hρdef]; linarith
  refine ⟨Real.sqrt (4 / ρ ^ 2 + 4 / ρ ^ 4), fun u h1 h2 => ?_⟩
  have hp1 : plev ξ u = 1 := by rw [plev_eq_exp hξ u, h1, Real.exp_zero]
  have hp2 : plev η u = 1 := by rw [plev_eq_exp hη u, h2, Real.exp_zero]
  simp only [plev] at hp1 hp2
  set c : ℝ := inner ℝ u ξ with hcdef
  have ht : tpart u = 1 + c := by linarith
  have heq : inner ℝ u η = c := by linarith
  set z : E n := u - c • ξ with hzdef
  have hut : u = z + c • ξ := by rw [hzdef]; abel
  have hzξ : inner ℝ z ξ = 0 := by
    rw [hzdef, inner_sub_left, hcdef, real_inner_smul_left, real_inner_self_eq_norm_sq, hξn]
    ring
  have hnorm : ‖u‖ ^ 2 = ‖z‖ ^ 2 + c ^ 2 := by
    rw [hut, norm_add_sq_real, real_inner_smul_right, hzξ, norm_smul, Real.norm_eq_abs, hξn,
      mul_one, sq_abs]
    ring
  have ht2 : tpart u ^ 2 = 1 + ‖u‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hu2 : ‖u‖ ^ 2 = 2 * c + c ^ 2 := by
    have h : (1 + c) ^ 2 = tpart u ^ 2 := by rw [ht]
    nlinarith [h, ht2]
  have hz2 : ‖z‖ ^ 2 = 2 * c := by linarith [hnorm, hu2]
  have hc0 : 0 ≤ c := by nlinarith [hz2, sq_nonneg ‖z‖]
  have hzi : inner ℝ z η = c * ρ := by
    rw [hzdef, inner_sub_left, hcdef, real_inner_smul_left, heq, hρdef]; ring
  have hzle : ‖z‖ = Real.sqrt (2 * c) := by
    rw [← Real.sqrt_sq (norm_nonneg z), hz2]
  have hcs : |inner ℝ z η| ≤ Real.sqrt (2 * c) := by
    calc |inner ℝ z η| ≤ ‖z‖ * ‖η‖ := abs_real_inner_le_norm z η
      _ = Real.sqrt (2 * c) := by rw [hηn, mul_one, hzle]
  have hkey : c * ρ ≤ Real.sqrt (2 * c) := by
    have h1 : inner ℝ z η ≤ Real.sqrt (2 * c) := le_trans (le_abs_self _) hcs
    rwa [hzi] at h1
  have hmain : ‖u‖ ^ 2 ≤ 4 / ρ ^ 2 + 4 / ρ ^ 4 := by
    rcases eq_or_lt_of_le hc0 with hce | hcgt
    · have hzero : ‖u‖ ^ 2 = 0 := by rw [hu2, hce.symm]; ring
      rw [hzero]; positivity
    · have h2 : (c * ρ) ^ 2 ≤ (Real.sqrt (2 * c)) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hc0 (le_of_lt hρ)) hkey 2
      rw [Real.sq_sqrt (by linarith)] at h2
      have hc_le : c ≤ 2 / ρ ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [h2, hρ, hcgt]
      have hsq : c ^ 2 ≤ 4 / ρ ^ 4 := by
        have h4 : (4:ℝ) / ρ ^ 4 = (2 / ρ ^ 2) ^ 2 := by ring_nf
        rw [h4]
        have hM : 0 ≤ 2 / ρ ^ 2 := by positivity
        nlinarith [hc_le, hc0, hM]
      have hA : c * ρ ^ 4 ≤ 2 * ρ ^ 2 := by
        have := (le_div_iff₀ (by positivity : (0:ℝ) < ρ ^ 2)).mp hc_le
        nlinarith [this, hρ]
      have hB : c ^ 2 * ρ ^ 4 ≤ 4 := by
        have := (le_div_iff₀ (by positivity : (0:ℝ) < ρ ^ 4)).mp hsq
        linarith [this]
      have hden : (0:ℝ) < ρ ^ 4 := by positivity
      have h4 : (4:ℝ) / ρ ^ 2 + 4 / ρ ^ 4 = (4 * ρ ^ 2 + 4) / ρ ^ 4 := by
        field_simp
      rw [h4, le_div_iff₀ hden]
      nlinarith [hA, hB, hu2]
  calc ‖u‖ = Real.sqrt (‖u‖ ^ 2) := (Real.sqrt_sq (norm_nonneg u)).symm
    _ ≤ Real.sqrt (4 / ρ ^ 2 + 4 / ρ ^ 4) := Real.sqrt_le_sqrt hmain

/-- If `bd g ξ = ξ` and the Busemann cocycle of `g` at `ξ` vanishes, then `g` preserves every
horoball based at `ξ`. -/
theorem parab_horoball_equiv (hI : HypIsometryProp n)
    (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) (hfix : bd g ξ = ξ) (hc : bCocy g ξ = 0) :
    ∀ t : ℝ, ∀ u : E n, (u ∈ horoball ξ t ↔ g • u ∈ horoball ξ t) := by
  have hbus : ∀ u : E n, busemann ξ (g • u) = busemann ξ u + bCocy g ξ := by
    intro u
    have h := hI.2.2.2.2.2.2.2.2.2.2.2.2 g ξ u hξ
    rw [hfix] at h
    rw [show bCocy g ξ = busemann ξ (g • (0 : E n)) by rw [bCocy, hfix]]
    exact h
  intro t u
  simp only [horoball, Set.mem_ofPred_eq]
  rw [hbus u, hc]
  constructor <;> intro h <;> linarith

/-! ## Bilinearity of the Minkowski form over finite sums -/

theorem parab_mink_zero_left (y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (0 : Fin n ⊕ Fin 1 → ℝ) y = 0 := by
  simp [Hyper.mink]

theorem parab_mink_zero_right (x : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (0 : Fin n ⊕ Fin 1 → ℝ) = 0 := by
  simp [Hyper.mink]

theorem parab_mink_add_left (x x' y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (x + x') y = Hyper.mink x y + Hyper.mink x' y := by
  have h : ∀ a : Fin n ⊕ Fin 1 → ℝ, Hyper.mink a y =
      a ⬝ᵥ (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec y := fun a => rfl
  rw [h, h, h, add_dotProduct]

theorem parab_mink_add_right (x y y' : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (y + y') = Hyper.mink x y + Hyper.mink x y' := by
  have h : ∀ a : Fin n ⊕ Fin 1 → ℝ, Hyper.mink x a =
      x ⬝ᵥ (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)).mulVec a := fun a => rfl
  rw [h, h, h, Matrix.mulVec_add, dotProduct_add]

theorem parab_mink_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n ⊕ Fin 1 → ℝ)) (y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (∑ i ∈ s, f i) y = ∑ i ∈ s, Hyper.mink (f i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [parab_mink_zero_left]
  | insert a s has ih =>
      rw [Finset.sum_insert has, parab_mink_add_left, ih, Finset.sum_insert has]

theorem parab_mink_sum_right {ι : Type*} (s : Finset ι)
    (x : Fin n ⊕ Fin 1 → ℝ) (f : ι → (Fin n ⊕ Fin 1 → ℝ)) :
    Hyper.mink x (∑ i ∈ s, f i) = ∑ i ∈ s, Hyper.mink x (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [parab_mink_zero_right]
  | insert a s has ih =>
      rw [Finset.sum_insert has, parab_mink_add_right, ih, Finset.sum_insert has]

/-! ## Linearity of `spat` -/

theorem parab_spat_zero : Hyper.spat (0 : Fin n ⊕ Fin 1 → ℝ) = 0 := rfl

theorem parab_spat_add (a b : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.spat (a + b) = Hyper.spat a + Hyper.spat b := rfl

theorem parab_spat_smul (r : ℝ) (a : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.spat (r • a) = r • Hyper.spat a := rfl

theorem parab_spat_sub (a b : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.spat (a - b) = Hyper.spat a - Hyper.spat b := rfl

theorem parab_spat_sum {ι : Type*} (s : Finset ι) (f : ι → (Fin n ⊕ Fin 1 → ℝ)) :
    Hyper.spat (∑ i ∈ s, f i) = ∑ i ∈ s, Hyper.spat (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [parab_spat_zero]
  | insert a s has ih =>
      rw [Finset.sum_insert has, parab_spat_add, ih, Finset.sum_insert has]

theorem parab_cont_hdist_left (p : E n) : Continuous (fun z : E n => hdist p z) := by
  have harg : ∀ z : E n,
      hdist p z = Real.log (Hyper.cc p z + Real.sqrt (Hyper.cc p z ^ 2 - 1)) := by
    intro z
    have h1 : 1 ≤ Hyper.cc p z := one_le_cosh_hdist p z
    have h2 : Real.arcosh (Hyper.cc p z)
        = Real.log (Hyper.cc p z + Real.sqrt (Hyper.cc p z ^ 2 - 1)) := by
      rw [← Real.log_exp (Real.arcosh (Hyper.cc p z)), Real.exp_arcosh h1]
    rw [Hyper.hdist_eq_cc, h2]
  rw [show (fun z : E n => hdist p z)
      = fun z => Real.log (Hyper.cc p z + Real.sqrt (Hyper.cc p z ^ 2 - 1)) from funext harg]
  have hcc : Continuous (fun z : E n => Hyper.cc p z) := by
    simp only [Hyper.cc]
    exact (continuous_const.mul continuous_tpart).sub (continuous_const.inner continuous_id)
  refine Continuous.log (hcc.add ((hcc.pow 2).sub continuous_const).sqrt) (fun z => ?_)
  have h1 : 1 ≤ Hyper.cc p z := one_le_cosh_hdist p z
  have h2 : 0 ≤ Real.sqrt (Hyper.cc p z ^ 2 - 1) := Real.sqrt_nonneg _
  linarith

/-! ## Escaping to the boundary -/

/-- A sequence whose `g`-displacement tends to `0` for a fixed-point-free isometry `g` escapes to
the boundary: some subsequence of the normalised points `(tpart (u k))⁻¹ • u k` converges to a
point of `Sph n`. -/
theorem parab_escape (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hg : IsParabolic g) (u : ℕ → E n)
    (hu : Tendsto (fun k => hdist (u k) (g • u k)) atTop (nhds 0)) :
    ∃ ξ : E n, ξ ∈ Sph n ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => (tpart (u (φ k)))⁻¹ • u (φ k)) atTop (nhds ξ) := by
  obtain ⟨-, -, -, hone, hmul, hfaith, hcont, hbdmem, -, -, -, -⟩ := hA
  obtain ⟨-, hsymm, heq0, htri, hcontHD, hball, hisom, -, -, -, -, -, -⟩ := hI
  have hwmem : ∀ k : ℕ, (tpart (u k))⁻¹ • u k ∈ Metric.closedBall (0 : E n) 1 := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt (parab_norm_smul_tpart_inv_lt_one (u k))
  obtain ⟨ξ, hξmem, φ, hφ, hξlim⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : E n) 1) hwmem
  refine ⟨ξ, ?_, φ, hφ, hξlim⟩
  have hξle : ‖ξ‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hξmem
  rw [mem_Sph_iff]
  by_contra hne
  have hlt : ‖ξ‖ < 1 := lt_of_le_of_ne hξle hne
  obtain ⟨r, hr1, hr2⟩ := exists_between hlt
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg ξ) hr1
  have hr2' : 0 < 1 - r ^ 2 := by nlinarith
  have hev : ∀ᶠ k in atTop, ‖(tpart (u (φ k)))⁻¹ • u (φ k)‖ ≤ r :=
    hξlim.norm.eventually (eventually_le_nhds hr1)
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  set K : ℝ := r / Real.sqrt (1 - r ^ 2) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]; exact le_of_lt (div_pos hr0 (Real.sqrt_pos.mpr hr2'))
  have hbound : ∀ k : ℕ, ‖u (φ (N + k))‖ ≤ K := by
    intro k
    have hk := hN (N + k) (by omega)
    rw [parab_norm_smul_tpart_inv] at hk
    have h1 : ‖u (φ (N + k))‖ ≤ r * tpart (u (φ (N + k))) := by
      rw [div_le_iff₀ (tpart_pos _)] at hk; linarith
    exact parab_norm_le_of_le_mul_tpart (le_of_lt hr0) hr2 h1
  obtain ⟨p, -, ψ, hψ, hplim⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : E n) K)
      (fun k => by rw [Metric.mem_closedBall, dist_zero_right]; exact hbound k)
  have hidx : Tendsto (fun k => φ (N + ψ k)) atTop atTop :=
    StrictMono.tendsto_atTop (fun a b hab => hφ (by have := hψ hab; omega))
  have hzero : Tendsto (fun k => hdist (u (φ (N + ψ k))) (g • u (φ (N + ψ k)))) atTop (nhds 0) :=
    hu.comp hidx
  have hp : Tendsto (fun k => u (φ (N + ψ k))) atTop (nhds p) := hplim
  have hdistp : Continuous (fun z : E n => hdist p z) := parab_cont_hdist_left p
  have hlim2 : Tendsto (fun k => hdist p (u (φ (N + ψ k)))) atTop (nhds 0) := by
    have h := (hdistp.tendsto p).comp hp
    have hpp : hdist p p = 0 := (heq0 p p).mpr rfl
    rwa [hpp] at h
  have h5 : hdist p (g • p) ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have h6 : ∀ᶠ k in atTop, 2 * hdist p (u (φ (N + ψ k)))
        + hdist (u (φ (N + ψ k))) (g • u (φ (N + ψ k))) < hdist p (g • p) :=
      ((hlim2.const_mul 2).add hzero).eventually
        (eventually_lt_nhds (by linarith : 2 * 0 + 0 < hdist p (g • p)))
    have h7 : ∀ k, hdist p (g • p) ≤ 2 * hdist p (u (φ (N + ψ k)))
        + hdist (u (φ (N + ψ k))) (g • u (φ (N + ψ k))) := by
      intro k
      have h1 := htri p (u (φ (N + ψ k))) (g • p)
      have h2 := htri (u (φ (N + ψ k))) (g • u (φ (N + ψ k))) (g • p)
      rw [hisom g (u (φ (N + ψ k))) p] at h2
      have h3 : hdist (u (φ (N + ψ k))) p = hdist p (u (φ (N + ψ k))) := hsymm _ _
      linarith
    obtain ⟨k, hk1, hk2⟩ := (h6.and (Filter.Eventually.of_forall h7)).exists
    linarith
  have hfix : hdist p (g • p) = 0 := le_antisymm h5 (hdist_nonneg _ _)
  exact hg.1 p ((heq0 p (g • p)).mp hfix).symm

/-! ## Bounded orbits have fixed points -/

/-- An isometry of `ℍⁿ` whose forward orbit of `0` is bounded fixes a point. The fixed point is
obtained as a limit of normalised projective means in the hyperboloid model. -/
theorem parab_bdd_orbit_fixed (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (R : ℝ) (hR : ∀ k : ℕ, ‖(g ^ k) • (0 : E n)‖ ≤ R) :
    ∃ u : E n, g • u = u := by
  obtain ⟨-, hcoesmul, -, hone, hmul, hfaith, hcont, -, -, -, -, -⟩ := hA
  obtain ⟨-, -, heq0, htri, hcontHD, hball, hisom, -, -, -, -, -, -⟩ := hI
  let x : ℕ → E n := fun k => (g ^ k) • (0 : E n)
  have hxdef : ∀ k, x k = (g ^ k) • (0 : E n) := fun k => rfl
  have hxstep : ∀ k, x (k+1) = g • x k := by
    intro k
    rw [hxdef, hxdef, pow_succ', hmul]
  have hxR : ∀ k, ‖x k‖ ≤ R := fun k => hR k
  have hrep : (rep g : PO n 1) = g := Quotient.out_eq g
  have hgsmul : ∀ w : E n, g • w = actO (rep g) w := by
    intro w
    have h := hcoesmul (rep g) w
    rw [hrep] at h
    exact h
  have hMrel : ∀ k, (mat (rep g)).mulVec (hlift (x k)) = tsign (rep g) • hlift (x (k+1)) := by
    intro k
    have h := Hyper.hlift_actO (rep g) (x k)
    rw [← hgsmul (x k), ← hxstep k] at h
    have h' : tsign (rep g) • hlift (x (k+1)) = (mat (rep g)).mulVec (hlift (x k)) := by
      rw [h, smul_smul, Hyper.tsign_mul_self, one_smul]
    exact h'.symm
  let S : ℕ → (Fin n ⊕ Fin 1 → ℝ) := fun N => ∑ k ∈ Finset.range N, hlift (x k)
  let S' : ℕ → (Fin n ⊕ Fin 1 → ℝ) := fun N => ∑ k ∈ Finset.range N, hlift (x (k+1))
  have hMsum : ∀ N, (mat (rep g)).mulVec (S N) = tsign (rep g) • S' N := by
    intro N
    rw [show S N = ∑ k ∈ Finset.range N, hlift (x k) from rfl,
      show S' N = ∑ k ∈ Finset.range N, hlift (x (k+1)) from rfl,
      Matrix.mulVec_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun k _ => hMrel k)
  let m : ℕ → (Fin n ⊕ Fin 1 → ℝ) := fun N => (N : ℝ)⁻¹ • S N
  let m' : ℕ → (Fin n ⊕ Fin 1 → ℝ) := fun N => (N : ℝ)⁻¹ • S' N
  have hMm : ∀ N, (mat (rep g)).mulVec (m N) = tsign (rep g) • m' N := by
    intro N
    rw [show m N = (N : ℝ)⁻¹ • S N from rfl, show m' N = (N : ℝ)⁻¹ • S' N from rfl,
      Matrix.mulVec_smul, hMsum N, smul_smul, smul_smul, mul_comm]
  have hminkS : ∀ N, Hyper.mink (S N) (S N) =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
        Hyper.mink (hlift (x i)) (hlift (x j)) := by
    intro N
    rw [show S N = ∑ k ∈ Finset.range N, hlift (x k) from rfl, parab_mink_sum_left]
    exact Finset.sum_congr rfl (fun i _ => parab_mink_sum_right _ _ _)
  have hminkS_bound : ∀ N, Hyper.mink (S N) (S N) ≤ -(N : ℝ) ^ 2 := by
    intro N
    rw [hminkS N]
    calc ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, Hyper.mink (hlift (x i)) (hlift (x j))
        ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, (-1 : ℝ) := by
          apply Finset.sum_le_sum; intro i _
          apply Finset.sum_le_sum; intro j _
          rw [Hyper.mink_hlift]
          have h := one_le_cosh_hdist (x i) (x j)
          linarith
      _ = -(N : ℝ) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  have hminkm : ∀ N, Hyper.mink (m N) (m N) =
      (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * Hyper.mink (S N) (S N) := by
    intro N
    rw [show m N = (N : ℝ)⁻¹ • S N from rfl, Hyper.mink_smul]
  have hminkm_le : ∀ N, 1 ≤ N → Hyper.mink (m N) (m N) ≤ -1 := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [hminkm N]
    have h1 : (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (-(N : ℝ) ^ 2) = -1 := by field_simp
    calc (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * Hyper.mink (S N) (S N)
        ≤ (N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (-(N : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left (hminkS_bound N) (by positivity)
      _ = -1 := h1
  have hminkm' : ∀ N, Hyper.mink (m' N) (m' N) = Hyper.mink (m N) (m N) := by
    intro N
    have h := Hyper.mink_mulVec (mat (rep g)) (Hyper.mat_conj (rep g)) (m N) (m N)
    rw [hMm N, Hyper.mink_smul, Hyper.tsign_mul_self, one_mul] at h
    exact h
  let cN : ℕ → ℝ := fun N => Real.sqrt (-(Hyper.mink (m N) (m N)))
  let u : ℕ → E n := fun N => Hyper.spat ((cN N)⁻¹ • m N)
  let u' : ℕ → E n := fun N => Hyper.spat ((cN N)⁻¹ • m' N)
  have hcN_ge : ∀ N, 1 ≤ N → 1 ≤ cN N := by
    intro N hN
    have h := hminkm_le N hN
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (-(Hyper.mink (m N) (m N))) := Real.sqrt_le_sqrt (by linarith)
  have hcN_pos : ∀ N, 1 ≤ N → 0 < cN N :=
    fun N hN => lt_of_lt_of_le zero_lt_one (hcN_ge N hN)
  have hcN_sq : ∀ N, 1 ≤ N → cN N ^ 2 = -(Hyper.mink (m N) (m N)) :=
    fun N hN => Real.sq_sqrt (by linarith [hminkm_le N hN])
  have hmtime : ∀ N, 1 ≤ N → 0 < (m N) (Sum.inr 0) := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hS0 : (S N) (Sum.inr 0) = ∑ k ∈ Finset.range N, tpart (x k) := by
      rw [show S N = ∑ k ∈ Finset.range N, hlift (x k) from rfl, Finset.sum_apply]
      exact Finset.sum_congr rfl (fun k _ => rfl)
    have hpos : 0 < ∑ k ∈ Finset.range N, tpart (x k) := by
      refine Finset.sum_pos' (fun k _ => le_of_lt (tpart_pos _)) ⟨0, ?_, tpart_pos _⟩
      rw [Finset.mem_range]; omega
    rw [show m N = (N : ℝ)⁻¹ • S N from rfl, Pi.smul_apply, smul_eq_mul, hS0]
    exact mul_pos (inv_pos.mpr hN0) hpos
  have hm'time : ∀ N, 1 ≤ N → 0 < (m' N) (Sum.inr 0) := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hS0 : (S' N) (Sum.inr 0) = ∑ k ∈ Finset.range N, tpart (x (k+1)) := by
      rw [show S' N = ∑ k ∈ Finset.range N, hlift (x (k+1)) from rfl, Finset.sum_apply]
      exact Finset.sum_congr rfl (fun k _ => rfl)
    have hpos : 0 < ∑ k ∈ Finset.range N, tpart (x (k+1)) := by
      refine Finset.sum_pos' (fun k _ => le_of_lt (tpart_pos _)) ⟨0, ?_, tpart_pos _⟩
      rw [Finset.mem_range]; omega
    rw [show m' N = (N : ℝ)⁻¹ • S' N from rfl, Pi.smul_apply, smul_eq_mul, hS0]
    exact mul_pos (inv_pos.mpr hN0) hpos
  have hmink_smul_neg : ∀ N, 1 ≤ N → Hyper.mink ((cN N)⁻¹ • m N) ((cN N)⁻¹ • m N) = -1 := by
    intro N hN
    have h2 : Hyper.mink (m N) (m N) = -((cN N) * (cN N)) := by
      rw [← pow_two]
      linarith [hcN_sq N hN]
    rw [Hyper.mink_smul, h2]
    have h1 : (cN N)⁻¹ * cN N = 1 := inv_mul_cancel₀ (ne_of_gt (hcN_pos N hN))
    calc (cN N)⁻¹ * (cN N)⁻¹ * -((cN N) * (cN N))
        = -((cN N)⁻¹ * cN N) * ((cN N)⁻¹ * cN N) := by ring
      _ = -1 := by rw [h1]; ring
  have huN : ∀ N, 1 ≤ N → hlift (u N) = (cN N)⁻¹ • m N := by
    intro N hN
    exact Hyper.hlift_spat_of_mink _ (hmink_smul_neg N hN)
      (by rw [Pi.smul_apply, smul_eq_mul]; exact mul_pos (inv_pos.mpr (hcN_pos N hN)) (hmtime N hN))
  have hu'N : ∀ N, 1 ≤ N → hlift (u' N) = (cN N)⁻¹ • m' N := by
    intro N hN
    refine Hyper.hlift_spat_of_mink _ ?_
      (by rw [Pi.smul_apply, smul_eq_mul]; exact mul_pos (inv_pos.mpr (hcN_pos N hN)) (hm'time N hN))
    rw [Hyper.mink_smul, hminkm' N, ← Hyper.mink_smul]
    exact hmink_smul_neg N hN
  have hMm' : ∀ N, tsign (rep g) • (mat (rep g)).mulVec (m N) = m' N := by
    intro N
    rw [hMm N, smul_smul, Hyper.tsign_mul_self, one_smul]
  have hgu : ∀ N, 1 ≤ N → g • u N = u' N := by
    intro N hN
    apply Hyper.hlift_injective
    calc hlift (g • u N)
        = tsign (rep g) • (mat (rep g)).mulVec ((cN N)⁻¹ • m N) := by
          rw [hgsmul (u N), Hyper.hlift_actO, huN N hN]
      _ = tsign (rep g) • ((cN N)⁻¹ • (mat (rep g)).mulVec (m N)) := by rw [Matrix.mulVec_smul]
      _ = (cN N)⁻¹ • (tsign (rep g) • (mat (rep g)).mulVec (m N)) := by rw [smul_comm]
      _ = (cN N)⁻¹ • m' N := by rw [hMm' N]
      _ = hlift (u' N) := (hu'N N hN).symm
  have htel : ∀ N, 1 ≤ N → Hyper.spat (S N - S' N) = x 0 - x N := by
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have h1 : S (M+1) - S' (M+1) = hlift (x 0) - hlift (x (M+1)) := by
      rw [show S (M+1) = ∑ k ∈ Finset.range (M+1), hlift (x k) from rfl,
        show S' (M+1) = ∑ k ∈ Finset.range (M+1), hlift (x (k+1)) from rfl,
        Finset.sum_range_succ', Finset.sum_range_succ]
      abel
    rw [h1, parab_spat_sub, Hyper.spat_hlift, Hyper.spat_hlift]
  have hdiff : ∀ N, 1 ≤ N → ‖u N - u' N‖ ≤ 2 * R / N := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hmN : m N - m' N = (N : ℝ)⁻¹ • (S N - S' N) := by
      rw [show m N = (N : ℝ)⁻¹ • S N from rfl, show m' N = (N : ℝ)⁻¹ • S' N from rfl,
        ← smul_sub]
    have h1 : u N - u' N = ((cN N)⁻¹ * (N : ℝ)⁻¹) • (x 0 - x N) := by
      rw [show u N = Hyper.spat ((cN N)⁻¹ • m N) from rfl,
        show u' N = Hyper.spat ((cN N)⁻¹ • m' N) from rfl,
        ← parab_spat_sub, ← smul_sub, parab_spat_smul, hmN, parab_spat_smul, htel N hN,
        smul_smul]
    have hx : ‖x 0 - x N‖ ≤ 2 * R := by
      calc ‖x 0 - x N‖ ≤ ‖x 0‖ + ‖x N‖ := norm_sub_le _ _
        _ ≤ R + R := add_le_add (hxR 0) (hxR N)
        _ = 2 * R := by ring
    calc ‖u N - u' N‖ = |(cN N)⁻¹ * (N : ℝ)⁻¹| * ‖x 0 - x N‖ := by
          rw [h1, norm_smul, Real.norm_eq_abs]
      _ ≤ (1 * (N : ℝ)⁻¹) * (2 * R) := by
          apply mul_le_mul
          · rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt (hcN_pos N hN)))
              (inv_nonneg.mpr (le_of_lt hN0)))]
            exact mul_le_mul_of_nonneg_right
              ((inv_le_one₀ (hcN_pos N hN)).mpr (hcN_ge N hN))
              (inv_nonneg.mpr (le_of_lt hN0))
          · exact hx
          · exact norm_nonneg _
          · exact mul_nonneg zero_le_one (inv_nonneg.mpr (le_of_lt hN0))
      _ = 2 * R / N := by rw [one_mul, div_eq_mul_inv, mul_comm]
  have hbdd_u : ∀ N, 1 ≤ N → ‖u N‖ ≤ R := by
    intro N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have h1 : u N = ((cN N)⁻¹ * (N : ℝ)⁻¹) • (∑ k ∈ Finset.range N, x k) := by
      rw [show u N = Hyper.spat ((cN N)⁻¹ • m N) from rfl, parab_spat_smul,
        show m N = (N : ℝ)⁻¹ • S N from rfl, parab_spat_smul, parab_spat_sum, smul_smul]
      rfl
    have hsum : ‖∑ k ∈ Finset.range N, x k‖ ≤ N * R := by
      calc ‖∑ k ∈ Finset.range N, x k‖ ≤ ∑ k ∈ Finset.range N, ‖x k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range N, R := Finset.sum_le_sum (fun k _ => hxR k)
        _ = N * R := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hcoef : (cN N)⁻¹ * (N : ℝ)⁻¹ ≤ 1 := by
      have h1 : (cN N)⁻¹ ≤ 1 := (inv_le_one₀ (hcN_pos N hN)).mpr (hcN_ge N hN)
      have h2 : (N : ℝ)⁻¹ ≤ 1 := by
        rw [inv_le_one₀ hN0]; exact_mod_cast hN
      nlinarith [h1, h2, inv_nonneg.mpr (le_of_lt (hcN_pos N hN)),
        inv_nonneg.mpr (le_of_lt hN0)]
    calc ‖u N‖ = |(cN N)⁻¹ * (N : ℝ)⁻¹| * ‖∑ k ∈ Finset.range N, x k‖ := by
          rw [h1, norm_smul, Real.norm_eq_abs]
      _ ≤ (N : ℝ)⁻¹ * (N * R) := by
          apply mul_le_mul
          · rw [abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (le_of_lt (hcN_pos N hN)))
              (inv_nonneg.mpr (le_of_lt hN0)))]
            simpa using mul_le_mul_of_nonneg_right ((inv_le_one₀ (hcN_pos N hN)).mpr
              (hcN_ge N hN)) (inv_nonneg.mpr (le_of_lt hN0))
          · exact hsum
          · exact norm_nonneg _
          · exact inv_nonneg.mpr (le_of_lt hN0)
      _ = R := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hN0), one_mul]
  -- compactness
  obtain ⟨p, -, ψ, hψ, hplim⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : E n) R)
      (fun k => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hbdd_u (k + 1) (Nat.le_add_left 1 k))
  have hp : Tendsto (fun k => u (ψ k + 1)) atTop (nhds p) := hplim
  have hd0 : Tendsto (fun N : ℕ => ‖u (N + 1) - u' (N + 1)‖) atTop (nhds 0) := by
    apply squeeze_zero (fun N => norm_nonneg _)
    · intro N
      simpa [Nat.cast_add, Nat.cast_one] using hdiff (N + 1) (Nat.le_add_left 1 N)
    · have h2 : Tendsto (fun N : ℕ => 2 * R * (1 / ((N : ℝ) + 1))) atTop (nhds (2 * R * 0)) :=
        tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [div_eq_mul_inv] using h2
  have hd : Tendsto (fun N : ℕ => ‖u' (N + 1) - u (N + 1)‖) atTop (nhds 0) := by
    simpa only [norm_sub_rev] using hd0
  have hdψ : Tendsto (fun k => u' (ψ k + 1) - u (ψ k + 1)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact hd.comp (StrictMono.tendsto_atTop hψ)
  have hp' : Tendsto (fun k => u' (ψ k + 1)) atTop (nhds p) := by
    have h := hp.add hdψ
    have h2 : (fun k => u (ψ k + 1) + (u' (ψ k + 1) - u (ψ k + 1)))
        = fun k => u' (ψ k + 1) := by
      funext k; abel
    rw [h2] at h
    simpa using h
  have hgp : Tendsto (fun k => g • u (ψ k + 1)) atTop (nhds (g • p)) :=
    ((hcont.comp (continuous_const.prodMk continuous_id)).tendsto p).comp hp
  have hsame : (fun k => g • u (ψ k + 1)) = fun k => u' (ψ k + 1) :=
    funext (fun k => hgu (ψ k + 1) (Nat.le_add_left 1 (ψ k)))
  have hgpp : Tendsto (fun k => u' (ψ k + 1)) atTop (nhds (g • p)) := by
    rw [← hsame]; exact hgp
  have : g • p = p := tendsto_nhds_unique hgpp hp'
  exact ⟨p, this⟩

/-! ## Existence and uniqueness of the boundary fixed point -/

/-- A parabolic isometry has a fixed point on the boundary sphere. -/
theorem parab_exists_fixed (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hg : IsParabolic g) :
    ∃ ξ : E n, ξ ∈ Sph n ∧ bd g ξ = ξ := by
  have hA' := hA
  have hI' := hI
  obtain ⟨-, -, -, hone, hmul, hfaith, hcont, hbdmem, hbdone, hbdmul, -, -⟩ := hA
  obtain ⟨-, hsymm, heq0, htri, hcontHD, hball, hisom, -, -, -, -, -, hbus⟩ := hI
  have hmin : ∀ k : ℕ, ∃ u : E n, hdist u (g • u) < 1 / ((k : ℝ) + 1) :=
    fun k => hg.2 _ (by positivity)
  choose u hu' using hmin
  have hdelta : Tendsto (fun k => hdist (u k) (g • u k)) atTop (nhds 0) :=
    squeeze_zero (fun k => hdist_nonneg _ _) (fun k => le_of_lt (hu' k))
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨ξ, hξS, φ, hφ, hξlim⟩ := parab_escape hA' hI' g hg u hdelta
  refine ⟨ξ, hξS, ?_⟩
  set ζ : E n := bd g ξ with hζdef
  have hζS : ζ ∈ Sph n := hbdmem g ξ hξS
  set c : ℝ := busemann ζ (g • (0 : E n)) with hcdef
  have hAlim : Tendsto (fun k => busemann ξ (u (φ k)) - busemann ζ (u (φ k))) atTop (nhds (-c)) := by
    have hb : ∀ k, ‖busemann ξ (u (φ k)) + c - busemann ζ (u (φ k))‖
        ≤ hdist (u (φ k)) (g • u (φ k)) := by
      intro k
      have hcc : busemann ζ (g • u (φ k)) = busemann ξ (u (φ k)) + c := by
        have h := hbus g ξ (u (φ k)) hξS
        rw [← hζdef, ← hcdef] at h
        exact h
      have hlip := ParabolicBusemannLip n hI' ζ hζS (g • u (φ k)) (u (φ k))
      rw [Real.norm_eq_abs, hsymm,
        show busemann ξ (u (φ k)) + c - busemann ζ (u (φ k))
            = busemann ζ (g • u (φ k)) - busemann ζ (u (φ k)) from by rw [hcc]]
      exact hlip
    have h1 : Tendsto (fun k => busemann ξ (u (φ k)) + c - busemann ζ (u (φ k))) atTop (nhds 0) :=
      squeeze_zero_norm hb (hdelta.comp (StrictMono.tendsto_atTop hφ))
    have h2 := h1.sub_const c
    have h3 : (fun k => (busemann ξ (u (φ k)) + c - busemann ζ (u (φ k))) - c)
        = fun k => busemann ξ (u (φ k)) - busemann ζ (u (φ k)) := by
      funext k; ring
    rw [h3] at h2
    simpa using h2
  by_contra hne
  have hγlt : inner ℝ ξ ζ < 1 := by
    have hξn : ‖ξ‖ = 1 := parab_sphere_norm hξS
    have hζn : ‖ζ‖ = 1 := parab_sphere_norm hζS
    have hpos : 0 < ‖ξ - ζ‖ ^ 2 := by
      have hne' : ξ - ζ ≠ 0 := sub_ne_zero.mpr (fun h => hne h.symm)
      have := norm_pos_iff.mpr hne'
      exact pow_pos this 2
    rw [norm_sub_sq_real, hξn, hζn] at hpos
    linarith
  have hnum : ∀ k, 0 < 1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ := by
    intro k
    have h1 : inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ ≤ ‖(tpart (u (φ k)))⁻¹ • u (φ k)‖ * ‖ξ‖ :=
      real_inner_le_norm _ _
    have h2 : ‖(tpart (u (φ k)))⁻¹ • u (φ k)‖ < 1 := parab_norm_smul_tpart_inv_lt_one _
    have h3 : ‖ξ‖ = 1 := parab_sphere_norm hξS
    rw [h3, mul_one] at h1
    linarith
  have hden : ∀ k, 0 < 1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ := by
    intro k
    have h1 : inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ ≤ ‖(tpart (u (φ k)))⁻¹ • u (φ k)‖ * ‖ζ‖ :=
      real_inner_le_norm _ _
    have h2 : ‖(tpart (u (φ k)))⁻¹ • u (φ k)‖ < 1 := parab_norm_smul_tpart_inv_lt_one _
    have h3 : ‖ζ‖ = 1 := parab_sphere_norm hζS
    rw [h3, mul_one] at h1
    linarith
  have hp : Tendsto (fun k => inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ) atTop (nhds 1) := by
    have hlim : Tendsto (fun k => inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ) atTop
        (nhds (inner ℝ ξ ξ)) :=
      ((continuous_id.inner continuous_const :
        Continuous (fun z : E n => inner ℝ z ξ)).tendsto ξ).comp hξlim
    rwa [show inner ℝ ξ ξ = 1 by simp [parab_sphere_norm hξS]] at hlim
  have hq : Tendsto (fun k => inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ) atTop
      (nhds (inner ℝ ξ ζ)) :=
    ((continuous_id.inner continuous_const :
      Continuous (fun z : E n => inner ℝ z ζ)).tendsto ξ).comp hξlim
  have hratio : Tendsto (fun k => (1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ)
      / (1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ)) atTop (nhds 0) := by
    have h1 : Tendsto (fun k => 1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ) atTop (nhds 0) := by
      have hcst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      simpa using hcst.sub hp
    have h2 : Tendsto (fun k => (1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ)⁻¹) atTop
        (nhds (1 - inner ℝ ξ ζ)⁻¹) :=
      (tendsto_const_nhds.sub hq).inv₀ (by linarith)
    have := h1.mul h2
    simpa [div_eq_mul_inv, mul_zero] using this
  have hlog : Tendsto (fun k => Real.log ((1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ)
      / (1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ))) atTop atBot := by
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hratio, Filter.Eventually.of_forall (fun k => div_pos (hnum k) (hden k))⟩
  have hAeq : ∀ k, busemann ξ (u (φ k)) - busemann ζ (u (φ k))
      = Real.log ((1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ)
      / (1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ)) := by
    intro k
    rw [busemann, busemann,
      ← Real.log_div (ne_of_gt (busemann_arg_pos ξ hξS _)) (ne_of_gt (busemann_arg_pos ζ hζS _))]
    congr 1
    rw [real_inner_smul_left, real_inner_smul_left]
    have htu : tpart (u (φ k)) ≠ 0 := ne_of_gt (tpart_pos _)
    rw [show tpart (u (φ k)) - inner ℝ (u (φ k)) ξ
          = tpart (u (φ k)) * (1 - (tpart (u (φ k)))⁻¹ * inner ℝ (u (φ k)) ξ) by
            rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ htu, one_mul],
      show tpart (u (φ k)) - inner ℝ (u (φ k)) ζ
          = tpart (u (φ k)) * (1 - (tpart (u (φ k)))⁻¹ * inner ℝ (u (φ k)) ζ) by
            rw [mul_sub, mul_one, ← mul_assoc, mul_inv_cancel₀ htu, one_mul],
      mul_div_mul_left _ _ htu]
  have hlog' : Tendsto (fun k => busemann ξ (u (φ k)) - busemann ζ (u (φ k))) atTop atBot := by
    rw [show (fun k => busemann ξ (u (φ k)) - busemann ζ (u (φ k)))
        = fun k => Real.log ((1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ξ)
        / (1 - inner ℝ ((tpart (u (φ k)))⁻¹ • u (φ k)) ζ)) from funext hAeq]
    exact hlog
  obtain ⟨k, hk1, hk2⟩ := ((hAlim.eventually
      (isOpen_Ioi.mem_nhds (show -c - 1 < -c by linarith))).and
    ((Filter.tendsto_atBot.mp hlog') (-c - 1))).exists
  linarith

/-- A parabolic isometry has at most one fixed point on the boundary sphere. -/
theorem parab_fixed_unique (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hg : IsParabolic g) (ξ η : E n) (hξS : ξ ∈ Sph n) (hηS : η ∈ Sph n)
    (hξ : bd g ξ = ξ) (hη : bd g η = η) : ξ = η := by
  have hA' := hA
  have hI' := hI
  obtain ⟨-, -, -, hone, hmul, hfaith, hcont, hbdmem, hbdone, hbdmul, -, -⟩ := hA
  obtain ⟨-, -, heq0, htri, hcontHD, hball, hisom, -, -, -, -, -, hbus⟩ := hI
  by_contra hne
  have hbusξ : ∀ w : E n, busemann ξ (g • w) = busemann ξ w := by
    intro w
    have h := hbus g ξ w hξS
    rw [hξ] at h
    have hc : busemann ξ (g • (0 : E n)) = bCocy g ξ := by rw [bCocy, hξ]
    rw [hc, bCocy_parabolic hA' hI' g hg ξ hξS hξ] at h
    simpa using h
  have hbusη : ∀ w : E n, busemann η (g • w) = busemann η w := by
    intro w
    have h := hbus g η w hηS
    rw [hη] at h
    have hc : busemann η (g • (0 : E n)) = bCocy g η := by rw [bCocy, hη]
    rw [hc, bCocy_parabolic hA' hI' g hg η hηS hη] at h
    simpa using h
  have hzeroξ : ∀ k : ℕ, busemann ξ ((g ^ k) • (0 : E n)) = 0 := by
    intro k
    induction k with
    | zero => rw [pow_zero, hone]; exact busemann_zero ξ
    | succ k ih =>
        rw [pow_succ', hmul, hbusξ, ih]
  have hzeroη : ∀ k : ℕ, busemann η ((g ^ k) • (0 : E n)) = 0 := by
    intro k
    induction k with
    | zero => rw [pow_zero, hone]; exact busemann_zero η
    | succ k ih =>
        rw [pow_succ', hmul, hbusη, ih]
  obtain ⟨R, hR⟩ := parab_exists_norm_bound hξS hηS hne
  have hRb : ∀ k : ℕ, ‖(g ^ k) • (0 : E n)‖ ≤ max R 0 :=
    fun k => le_trans (hR _ (hzeroξ k) (hzeroη k)) (le_max_left _ _)
  obtain ⟨u, hu⟩ := parab_bdd_orbit_fixed hA' hI' g (max R 0) hRb
  exact (hg.1 u) hu

end

end Work.Mostow

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Filter

theorem geomFiniteParabolicClass (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hg : IsParabolic g) :
    (∃ ξ : E n, ξ ∈ Sph n ∧ bd g ξ = ξ) ∧
    (∀ ξ η : E n, ξ ∈ Sph n → η ∈ Sph n → bd g ξ = ξ → bd g η = η → ξ = η) ∧
    (∀ ξ : E n, ξ ∈ Sph n → bd g ξ = ξ → ∀ t : ℝ, ∀ u : E n,
        (u ∈ horoball ξ t ↔ g • u ∈ horoball ξ t)) := by
  obtain ⟨ξ, hξS, hξfix⟩ := parab_exists_fixed hA hI g hg
  exact ⟨⟨ξ, hξS, hξfix⟩,
    fun ξ η hξ hη h1 h2 => parab_fixed_unique hA hI g hg ξ η hξ hη h1 h2,
    fun ξ hξ h1 t u => parab_horoball_equiv hI g hξ h1
      (bCocy_parabolic hA hI g hg ξ hξ h1) t u⟩

end Work.Mostow

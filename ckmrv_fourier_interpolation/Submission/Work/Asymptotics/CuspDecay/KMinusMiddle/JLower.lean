import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.All
import Submission.Work.Asymptotics.CuspDecay.PsiDefs
import Submission.Work.Asymptotics.CuspDecay.PsiBounds
import Submission.Work.Asymptotics.CuspDecay.PsiLipschitz
import Submission.Work.Asymptotics.CuspDecay.norm_one_sub_expm_ge_third
import Submission.Work.Asymptotics.CuspDecay.j_sub_lower_lattice
import Submission.Work.Asymptotics.MiddleRange.Classify
import Submission.Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general

set_option maxHeartbeats 1000000

/-!
# The lower bound for `‖j τ - j(i/s)‖` on the "middle" range

This file proves `Work.Asymptotics.CuspDecay.KMinusMiddle.JLower`.

For `s ≥ 37/20`, `τ ∈ 𝒟` with `|τ.im - s| ≤ 1/4` one has

`c · e^{2πs} · dist(τ, {i s - 1, i s, i s + 1}) ≤ ‖j τ - j (i/s)‖`

with a universal constant `c > 0`.  Since `j` is `SL(2,ℤ)`-invariant, `j (i/s) = j (i s)`, and
`j` has the same value at the three points `i s + k` (`k = 0, ±1`); thus the statement compares
`j τ` with its value on the `T`-orbit of `i s` and measures the distance to the *nearest* point
of that orbit.

Two regimes:

* `s ≥ 9/4`: then `τ.im ≥ 2` and `i s` has imaginary part `≥ 2`, so the `Ψ = q·j` estimate
  `Work.Asymptotics.CuspDecay.j_sub_lower_lattice` applies directly, with constant `1/8`.
* `37/20 ≤ s ≤ 9/4`: the whole configuration then lives in a *fixed compact* region of `ℍ`
  (`8/5 ≤ Im ≤ 5/2`, `|Re| ≤ 1/2` after removing the nearest integer, and `i s` on the compact
  arc `{i s : 37/20 ≤ s ≤ 9/4}`).  There the bound is pure compactness, in two steps:
  - away from the coincidence `τ = i s` one uses that `j τ = j (i s)` forces `τ = i s`
    (`eq_or_eq_S_of_re_eq_zero`) plus compactness of the (closed) parameter space;
  - near the coincidence one uses the local strict differentiability of `j` at the non-elliptic
    points `i s` (`exists_diffQuotient_lower_general`), uniformised over the compact arc by
    extracting a finite subcover.
-/

namespace Work.Asymptotics.CuspDecay.KMinusMiddle

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

/-! ## The two `j`-identifications -/

/-- `j (i/s) = j (i s)`: the modular `j`-invariant is `S`-invariant and `S • (i s) = i/s`. -/
lemma jInvariantFun_imagAxis_one_div (s : ℝ) (hs : 0 < s) :
    Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (1 / s) (by positivity))
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
  have hpt : ModularGroup.S • Work.Kernels.imagAxis s hs
      = Work.Kernels.imagAxis (1 / s) (by positivity) := by
    apply UpperHalfPlane.ext
    have hcoe : ((ModularGroup.S • Work.Kernels.imagAxis s hs : ℍ) : ℂ)
        = (-((Work.Kernels.imagAxis s hs : ℍ) : ℂ))⁻¹ :=
      congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (Work.Kernels.imagAxis s hs))
    rw [hcoe]
    show (-((s : ℂ) * Complex.I))⁻¹ = ((1 / s : ℝ) : ℂ) * Complex.I
    have h1 : ((1 / s : ℝ) : ℂ) = ((s : ℂ))⁻¹ := by
      rw [Complex.ofReal_div, Complex.ofReal_one, one_div]
    rw [h1, inv_neg, mul_inv, Complex.inv_I]
    ring
  rw [← hpt]
  exact Work.Kernels.KernelFacts.jInvariantFun_S_smul _

/-! ## The arc `{i s}` and the box `{8/5 ≤ Im ≤ 5/2, |Re| ≤ 1/2}` -/

/-- The point `i s` of the upper half plane. -/
def arcPt (s : ℝ) : ℍ := UpperHalfPlane.ofComplex (Complex.I * (s : ℂ))

lemma arcPt_coe (s : ℝ) (hs : 0 < s) : ((arcPt s : ℍ) : ℂ) = Complex.I * (s : ℂ) := by
  rw [arcPt, UpperHalfPlane.ofComplex_apply_of_im_pos (by simpa using hs)]

lemma arcPt_eq_imagAxis (s : ℝ) (hs : 0 < s) :
    arcPt s = Work.Kernels.imagAxis s hs := by
  apply UpperHalfPlane.ext
  rw [arcPt_coe s hs]
  show Complex.I * (s : ℂ) = (s : ℂ) * Complex.I
  exact mul_comm _ _

lemma arcPt_re (s : ℝ) (hs : 0 < s) : (arcPt s).re = 0 := by
  rw [← UpperHalfPlane.coe_re, arcPt_coe s hs]
  simp

/-- `S • (i s) = i/s`. -/
lemma S_smul_arcPt (s : ℝ) (hs : 0 < s) :
    ModularGroup.S • arcPt s = arcPt (1 / s) := by
  apply UpperHalfPlane.ext
  have hcoe : ((ModularGroup.S • arcPt s : ℍ) : ℂ) = (-((arcPt s : ℍ) : ℂ))⁻¹ :=
    congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (arcPt s))
  rw [hcoe, arcPt_coe s hs, arcPt_coe (1 / s) (by positivity)]
  have h1 : ((1 / s : ℝ) : ℂ) = ((s : ℂ))⁻¹ := by
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div]
  rw [h1, inv_neg, mul_inv, Complex.inv_I]
  ring

/-- The point `a + b i` of the upper half plane (`b > 0`). -/
def boxPt (a b : ℝ) (hb : 0 < b) : ℍ :=
  ⟨(a : ℂ) + (b : ℂ) * Complex.I, by simpa using hb⟩

lemma boxPt_coe (a b : ℝ) (hb : 0 < b) :
    ((boxPt a b hb : ℍ) : ℂ) = (a : ℂ) + (b : ℂ) * Complex.I := rfl

lemma boxPt_re (a b : ℝ) (hb : 0 < b) : (boxPt a b hb).re = a := by
  rw [← UpperHalfPlane.coe_re, boxPt_coe]; simp

lemma boxPt_im (a b : ℝ) (hb : 0 < b) : (boxPt a b hb).im = b := by
  rw [← UpperHalfPlane.coe_im, boxPt_coe]; simp

/-- The box `{8/5 ≤ Im ≤ 5/2, -1/2 ≤ Re ≤ 1/2}` of the local regime, exhibited as the
continuous image of a compact set of parameters. -/
def Jbox : Set ℍ :=
  Set.range (fun p : {p : ℝ × ℝ // p.1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
      p.2 ∈ Set.Icc (8 / 5 : ℝ) (5 / 2)} =>
    boxPt p.1.1 p.1.2 (by linarith [p.2.2.1]))

lemma mem_Jbox {u : ℍ} :
    u ∈ Jbox ↔ u.re ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
      u.im ∈ Set.Icc (8 / 5 : ℝ) (5 / 2) := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [boxPt_re, boxPt_im]
    exact p.2
  · rintro ⟨h1, h2⟩
    refine ⟨⟨(u.re, u.im), ⟨h1, h2⟩⟩, ?_⟩
    apply UpperHalfPlane.ext
    rw [boxPt_coe]
    have h := Complex.re_add_im (u : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    rw [← h]

lemma isCompact_Jbox : IsCompact Jbox := by
  have hcont : Continuous (fun p : {p : ℝ × ℝ // p.1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
      p.2 ∈ Set.Icc (8 / 5 : ℝ) (5 / 2)} =>
        boxPt p.1.1 p.1.2 (by linarith [p.2.2.1])) := by
    rw [continuous_induced_rng]
    change Continuous (fun p : {p : ℝ × ℝ // p.1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
      p.2 ∈ Set.Icc (8 / 5 : ℝ) (5 / 2)} => (p.1.1 : ℂ) + (p.1.2 : ℂ) * Complex.I)
    have h : Continuous (fun q : ℝ × ℝ => ((q.1 : ℝ) : ℂ) + ((q.2 : ℝ) : ℂ) * Complex.I) :=
      (Complex.continuous_ofReal.comp continuous_fst).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
    exact h.comp continuous_subtype_val
  have hcompSet : IsCompact {p : ℝ × ℝ | p.1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
      p.2 ∈ Set.Icc (8 / 5 : ℝ) (5 / 2)} := by
    have h : {p : ℝ × ℝ | p.1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
        p.2 ∈ Set.Icc (8 / 5 : ℝ) (5 / 2)}
        = Set.Icc (-(1 : ℝ) / 2, 8 / 5) ((1 : ℝ) / 2, 5 / 2) := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_Icc, Prod.le_def]
      tauto
    rw [h]
    exact isCompact_Icc
  haveI : CompactSpace {p : ℝ × ℝ // p.1 ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
      p.2 ∈ Set.Icc (8 / 5 : ℝ) (5 / 2)} := isCompact_iff_compactSpace.mp hcompSet
  simpa [Jbox, Set.image_univ] using isCompact_univ.image hcont

/-! ## The local strict-differentiability bound, uniform over the compact arc -/

/-- `j` expands distances near every `i s` with `s ≥ 37/20`, with constants depending on `s`.
This is `Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general` at `t₀ = s`. -/
lemma loc_exists (s : ℝ) (hs : 37 / 20 ≤ s) :
    ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧ ∀ u v : ℍ,
      ‖(u : ℂ) - Complex.I * (s : ℂ)‖ < p.1 →
      ‖(v : ℂ) - Complex.I * (s : ℂ)‖ < p.1 →
      p.2 * ‖(u : ℂ) - (v : ℂ)‖
        ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun v‖ := by
  have hs0 : 0 < s := by linarith
  have hne : s ≠ 1 := by rintro rfl; norm_num at hs
  obtain ⟨ρ, hρ, c, hc, hb⟩ :=
    Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general hs0 hne
  refine ⟨(ρ, c), hρ, hc, fun u v hu hv => ?_⟩
  have hcen : ((Work.Kernels.imagAxis s hs0 : ℍ) : ℂ) = Complex.I * (s : ℂ) := by
    show (s : ℂ) * Complex.I = Complex.I * (s : ℂ)
    exact mul_comm _ _
  simp only [hcen] at hb
  exact hb u v hu hv

/-- The chosen local constants at `i s`. -/
noncomputable def loc (s : ℝ) (h : 37 / 20 ≤ s) : ℝ × ℝ := Classical.choose (loc_exists s h)

lemma loc_pos (s : ℝ) (h : 37 / 20 ≤ s) : 0 < (loc s h).1 ∧ 0 < (loc s h).2 := by
  have hspec := Classical.choose_spec (loc_exists s h)
  unfold loc
  exact ⟨hspec.1, hspec.2.1⟩

lemma loc_bound (s : ℝ) (h : 37 / 20 ≤ s) (u v : ℍ)
    (hu : ‖(u : ℂ) - Complex.I * (s : ℂ)‖ < (loc s h).1)
    (hv : ‖(v : ℂ) - Complex.I * (s : ℂ)‖ < (loc s h).1) :
    (loc s h).2 * ‖(u : ℂ) - (v : ℂ)‖
      ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun v‖ := by
  have hspec := Classical.choose_spec (loc_exists s h)
  unfold loc
  exact hspec.2.2 u v hu hv

/-- **The local lower bound, uniform over the compact arc `{i s : 37/20 ≤ s ≤ 9/4}`.**  There
are `δ, c > 0` such that `‖j u - j v‖ ≥ c ‖u - v‖` for all `u, v` within `δ` of a point `i s`
of the arc.  The proof extracts a finite subcover of the arc by the local balls
`B(i s, ρ(s)/2)` supplied by `loc_exists`, and takes the minimum of the corresponding
constants. -/
theorem uniform_local_lower :
    ∃ δ c : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 0 < c ∧
      ∀ (s : ℝ) (hs : 37 / 20 ≤ s) (hs2 : s ≤ 9 / 4) (u v : ℍ),
        ‖(u : ℂ) - Complex.I * (s : ℂ)‖ < δ →
        ‖(v : ℂ) - Complex.I * (s : ℂ)‖ < δ →
        c * ‖(u : ℂ) - (v : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun v‖ := by
  set I : Type := {s : ℝ // s ∈ Set.Icc (37 / 20 : ℝ) (9 / 4)} with hI
  set A : Set ℂ := Set.range (fun s : I => Complex.I * (s.1 : ℂ)) with hA
  have hAc : IsCompact A := by
    have hcont : Continuous (fun s : I => Complex.I * (s.1 : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)
    haveI : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
    simpa [hA, Set.image_univ] using isCompact_univ.image hcont
  have hcover : A ⊆ ⋃ i : I,
      Metric.ball (Complex.I * (i.1 : ℂ)) ((loc i.1 i.2.1).1 / 2) := by
    rintro w ⟨s, rfl⟩
    refine Set.mem_iUnion.mpr ⟨s, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]
    have h := (loc_pos s.1 s.2.1).1
    linarith
  obtain ⟨t, ht⟩ := hAc.elim_finite_subcover
    (fun i : I => Metric.ball (Complex.I * (i.1 : ℂ)) ((loc i.1 i.2.1).1 / 2))
    (fun i => Metric.isOpen_ball) hcover
  have hAne : A.Nonempty :=
    ⟨Complex.I * ((37 / 20 : ℝ) : ℂ), ⟨⟨37 / 20, Set.mem_Icc.mpr ⟨le_rfl, by norm_num⟩⟩, rfl⟩⟩
  have htne : t.Nonempty := by
    rcases t.eq_empty_or_nonempty with h | h
    · exfalso
      obtain ⟨w, hw⟩ := hAne
      have := ht hw
      rw [h] at this
      simpa using this
    · exact h
  set δ₀ : ℝ := Finset.min' (t.image (fun i : I => (loc i.1 i.2.1).1 / 2))
      (htne.image (fun i : I => (loc i.1 i.2.1).1 / 2)) with hδ₀
  set c : ℝ := Finset.min' (t.image (fun i : I => (loc i.1 i.2.1).2))
      (htne.image (fun i : I => (loc i.1 i.2.1).2)) with hc
  have hδ₀mem := Finset.min'_mem (t.image (fun i : I => (loc i.1 i.2.1).1 / 2))
      (htne.image (fun i : I => (loc i.1 i.2.1).1 / 2))
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀]
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hδ₀mem
    rw [← hi]
    have h := (loc_pos i.1 i.2.1).1
    linarith
  have hcpos : 0 < c := by
    rw [hc]
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp
      (Finset.min'_mem (t.image (fun i : I => (loc i.1 i.2.1).2))
        (htne.image (fun i : I => (loc i.1 i.2.1).2)))
    rw [← hi]
    exact (loc_pos i.1 i.2.1).2
  refine ⟨min δ₀ (1 / 2), c, lt_min hδ₀pos (by norm_num), min_le_right _ _, hcpos, ?_⟩
  intro s hs hs2 u v hu hv
  have hsI : s ∈ Set.Icc (37 / 20 : ℝ) (9 / 4) := ⟨hs, hs2⟩
  have hmemA : Complex.I * (s : ℂ) ∈ A := ⟨⟨s, hsI⟩, rfl⟩
  have hmem := ht hmemA
  rw [Set.mem_iUnion] at hmem
  obtain ⟨i, hi⟩ := hmem
  rw [Set.mem_iUnion] at hi
  obtain ⟨hit, hiU⟩ := hi
  rw [Metric.mem_ball, dist_eq_norm] at hiU
  have hδle : min δ₀ (1 / 2) ≤ (loc i.1 i.2.1).1 / 2 :=
    le_trans (min_le_left _ _)
      (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hit, rfl⟩))
  have hcle : c ≤ (loc i.1 i.2.1).2 :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hit, rfl⟩)
  have hρpos : 0 < (loc i.1 i.2.1).1 := (loc_pos i.1 i.2.1).1
  have hu' : ‖(u : ℂ) - Complex.I * (i.1 : ℂ)‖ < (loc i.1 i.2.1).1 := by
    have h1 : ‖(u : ℂ) - Complex.I * (i.1 : ℂ)‖
        ≤ ‖(u : ℂ) - Complex.I * (s : ℂ)‖
          + ‖Complex.I * (s : ℂ) - Complex.I * (i.1 : ℂ)‖ := by
      have h2 := norm_add_le ((u : ℂ) - Complex.I * (s : ℂ))
        (Complex.I * (s : ℂ) - Complex.I * (i.1 : ℂ))
      have h3 : (u : ℂ) - Complex.I * (s : ℂ)
          + (Complex.I * (s : ℂ) - Complex.I * (i.1 : ℂ))
          = (u : ℂ) - Complex.I * (i.1 : ℂ) := by ring
      rwa [h3] at h2
    linarith
  have hv' : ‖(v : ℂ) - Complex.I * (i.1 : ℂ)‖ < (loc i.1 i.2.1).1 := by
    have h1 : ‖(v : ℂ) - Complex.I * (i.1 : ℂ)‖
        ≤ ‖(v : ℂ) - Complex.I * (s : ℂ)‖
          + ‖Complex.I * (s : ℂ) - Complex.I * (i.1 : ℂ)‖ := by
      have h2 := norm_add_le ((v : ℂ) - Complex.I * (s : ℂ))
        (Complex.I * (s : ℂ) - Complex.I * (i.1 : ℂ))
      have h3 : (v : ℂ) - Complex.I * (s : ℂ)
          + (Complex.I * (s : ℂ) - Complex.I * (i.1 : ℂ))
          = (v : ℂ) - Complex.I * (i.1 : ℂ) := by ring
      rwa [h3] at h2
    linarith
  have hmain := loc_bound i.1 i.2.1 u v hu' hv'
  calc c * ‖(u : ℂ) - (v : ℂ)‖ ≤ (loc i.1 i.2.1).2 * ‖(u : ℂ) - (v : ℂ)‖ :=
        mul_le_mul_of_nonneg_right hcle (norm_nonneg _)
    _ ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun v‖ := hmain

/-! ## The compactness bound away from the coincidence -/

/-- `S • (S • x) = x`. -/
lemma S_smul_S_smul_local (x : ℍ) : ModularGroup.S • (ModularGroup.S • x) = x := by
  apply UpperHalfPlane.ext
  rw [show ((ModularGroup.S • (ModularGroup.S • x) : ℍ) : ℂ)
        = (-(((ModularGroup.S • x : ℍ) : ℂ)))⁻¹ from
      congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul (ModularGroup.S • x))]
  rw [show (((ModularGroup.S • x : ℍ) : ℂ)) = (-(x : ℂ))⁻¹ from
      congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul x)]
  have hx : (x : ℂ) ≠ 0 := by
    intro h
    have hp := x.im_pos
    rw [← UpperHalfPlane.coe_im, h] at hp
    simp at hp
  field_simp

/-- `r ≤ ‖z‖` from `0 ≤ r ≤ z.re`. -/
lemma le_norm_of_re {z : ℂ} {r : ℝ} (h : r ≤ z.re) (hr : 0 ≤ r) : r ≤ ‖z‖ := by
  have h1 : z.re ≤ |z.re| := le_abs_self _
  have h2 := Complex.abs_re_le_norm z
  linarith

/-- The Euclidean distance `‖u - i s‖` as a function of the parameter `(u, s)`. -/
def arcDist (p : ℍ × ℝ) : ℝ := ‖(p.1 : ℂ) - Complex.I * (p.2 : ℂ)‖

lemma continuous_arcDist : Continuous arcDist := by
  unfold arcDist
  exact ((UpperHalfPlane.continuous_coe.comp continuous_fst).sub
    ((continuous_const : Continuous (fun _ : ℍ × ℝ => Complex.I)).mul
      (Complex.continuous_ofReal.comp continuous_snd))).norm

/-- `‖j u - j (i s)‖` as a function of the parameter `(u, s)`. -/
def jarc (p : ℍ × ℝ) : ℝ :=
  ‖Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (arcPt p.2)‖

/-- **The lower bound on the compact core.**  For `u` in the box `Jbox` and `s ∈ [37/20, 9/4]`
with `u` at distance `≥ δ > 0` from `i s`, the value `‖j u - j (i s)‖` is bounded below by a
positive constant.  This is compactness of the (closed) parameter space together with the fact
that `j u = j (i s)` forces `u = i s` (`eq_or_eq_S_of_re_eq_zero`). -/
theorem Jbox_norm_lower (δ : ℝ) (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℝ) (hs : 37 / 20 ≤ s) (hs2 : s ≤ 9 / 4) (u : ℍ),
      u ∈ Jbox → δ ≤ ‖(u : ℂ) - Complex.I * (s : ℂ)‖ →
      c ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun (arcPt s)‖ := by
  set T : Set (ℍ × ℝ) :=
    (Jbox ×ˢ Set.Icc (37 / 20 : ℝ) (9 / 4)) ∩ {p | δ ≤ arcDist p} with hT
  have hTc : IsCompact T := by
    rw [hT]
    exact (isCompact_Jbox.prod isCompact_Icc).inter_right
      (isClosed_le continuous_const continuous_arcDist)
  have hTbox : ∀ p ∈ T, p.1 ∈ Jbox ∧ p.2 ∈ Set.Icc (37 / 20 : ℝ) (9 / 4) := by
    intro p hp
    rw [hT] at hp
    exact hp.1
  have hTdist : ∀ p ∈ T, δ ≤ arcDist p := by
    intro p hp
    rw [hT] at hp
    exact hp.2
  have hTpos : ∀ p ∈ T, p.2 ∈ Set.Ioi (0 : ℝ) := fun p hp =>
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 37 / 20) (hTbox p hp).2.1
  have hcontF : ContinuousOn jarc T := by
    unfold jarc
    have hcj : Continuous (fun τ : ℍ => Work.Kernels.jInvariantFun τ) :=
      (Work.Asymptotics.CuspDecay.mdifferentiable_jInvariantFun).continuous
    have h1 : ContinuousOn (fun p : ℍ × ℝ => arcPt p.2) T :=
      UpperHalfPlane.continuousOn_ofComplex_I_mul.comp continuous_snd.continuousOn hTpos
    exact (ContinuousOn.sub
      (hcj.continuousOn.comp continuous_fst.continuousOn
        (fun p hp => Set.mem_univ _))
      (hcj.continuousOn.comp h1 (fun p hp => Set.mem_univ _))).norm
  have hTne : T.Nonempty := by
    refine ⟨(boxPt 0 (5 / 2) (by norm_num), 37 / 20), ?_⟩
    rw [hT]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_Jbox]
      exact ⟨⟨by norm_num [boxPt_re], by norm_num [boxPt_re]⟩,
        ⟨by norm_num [boxPt_im], by norm_num [boxPt_im]⟩⟩
    · exact ⟨le_rfl, by norm_num⟩
    · rw [Set.mem_setOf_eq]
      unfold arcDist
      have hnorm : (↑(boxPt 0 (5 / 2) (by norm_num) : ℍ) : ℂ)
            - Complex.I * ((37 / 20 : ℝ) : ℂ)
            = Complex.I * ((((13 : ℝ) / 20 : ℝ)) : ℂ) := by
        rw [boxPt_coe]
        push_cast
        ring
      rw [hnorm, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 13 / 20)]
      linarith [hδhalf]
  obtain ⟨p₀, hp₀T, hp₀min⟩ := hTc.exists_isMinOn hTne hcontF
  refine ⟨jarc p₀, ?_, ?_⟩
  · unfold jarc
    rw [norm_pos_iff]
    intro heq0
    have heq : Work.Kernels.jInvariantFun p₀.1 = Work.Kernels.jInvariantFun (arcPt p₀.2) :=
      sub_eq_zero.mp heq0
    have hbox : p₀.1 ∈ Jbox := (hTbox p₀ hp₀T).1
    have hmem : p₀.1.re ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) ∧
        p₀.1.im ∈ Set.Icc (8 / 5 : ℝ) (5 / 2) := mem_Jbox.mp hbox
    have him1 : (8 : ℝ) / 5 ≤ p₀.1.im := hmem.2.1
    have hspos : 0 < p₀.2 :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 37 / 20) (hTbox p₀ hp₀T).2.1
    have hpD : p₀.1 ∈ Work.Asymptotics.DomainD := by
      refine ⟨by linarith [hmem.1.1], by linarith [hmem.1.2], ?_, ?_⟩
      · have h := Complex.abs_im_le_norm ((p₀.1 : ℂ) - (1 / 2 : ℂ))
        have him : (((p₀.1 : ℂ) - (1 / 2 : ℂ))).im = p₀.1.im := by simp
        rw [him, abs_of_pos p₀.1.im_pos] at h
        linarith
      · have h := Complex.abs_im_le_norm ((p₀.1 : ℂ) + (1 / 2 : ℂ))
        have him : (((p₀.1 : ℂ) + (1 / 2 : ℂ))).im = p₀.1.im := by simp
        rw [him, abs_of_pos p₀.1.im_pos] at h
        linarith
    have hzre : ((arcPt p₀.2 : ℍ) : ℂ).re = 0 := by
      rw [arcPt_coe p₀.2 hspos]
      simp
    rcases Work.Asymptotics.eq_or_eq_S_of_re_eq_zero (τ := p₀.1) (z := arcPt p₀.2)
      hpD hzre heq with h | h
    · have hδle : δ ≤ arcDist p₀ := hTdist p₀ hp₀T
      unfold arcDist at hδle
      have hzero : ‖(p₀.1 : ℂ) - Complex.I * (p₀.2 : ℂ)‖ = 0 := by
        rw [← arcPt_coe p₀.2 hspos, h, sub_self, norm_zero]
      linarith [hδle, hδ]
    · have hcoe : Complex.I * (p₀.2 : ℂ) = (-(p₀.1 : ℂ))⁻¹ := by
        have h' := congrArg UpperHalfPlane.coe h
        rw [arcPt_coe p₀.2 hspos,
          congrArg UpperHalfPlane.coe (UpperHalfPlane.modular_S_smul p₀.1)] at h'
        exact h'
      have hppos : 0 < 1 / p₀.2 := div_pos one_pos hspos
      have h2 : p₀.1 = arcPt (1 / p₀.2) := by
        apply UpperHalfPlane.ext
        rw [arcPt_coe (1 / p₀.2) hppos]
        have h1 : ((1 / p₀.2 : ℝ) : ℂ) = ((p₀.2 : ℂ))⁻¹ := by
          rw [Complex.ofReal_div, Complex.ofReal_one, one_div]
        rw [h1]
        have h2' : (Complex.I * (p₀.2 : ℂ))⁻¹ = -(p₀.1 : ℂ) := by
          have := congrArg Inv.inv hcoe
          simpa using this
        have h3 : (Complex.I * (p₀.2 : ℂ))⁻¹ = -(Complex.I * ((p₀.2 : ℂ))⁻¹) := by
          rw [mul_inv, Complex.inv_I]; ring
        rw [h3] at h2'
        have h4 : Complex.I * ((p₀.2 : ℂ))⁻¹ = (p₀.1 : ℂ) := by
          have := congrArg Neg.neg h2'
          simpa using this
        exact h4.symm
      have him : p₀.1.im = 1 / p₀.2 := by
        rw [h2, ← UpperHalfPlane.coe_im, arcPt_coe (1 / p₀.2) hppos]
        simp
      have hle : 1 / p₀.2 ≤ 20 / 37 := by
        rw [div_le_iff₀ hspos]
        nlinarith [(hTbox p₀ hp₀T).2.1]
      linarith [him, him1, hle]
  · intro s hs hs2 u hu hdist
    have hmem : (u, s) ∈ T := by
      rw [hT]
      exact ⟨⟨hu, ⟨hs, hs2⟩⟩, by unfold arcDist; exact hdist⟩
    unfold jarc
    have hmin : jarc p₀ ≤ jarc (u, s) := hp₀min hmem
    have h1 : jarc p₀
        = ‖Work.Kernels.jInvariantFun p₀.1 - Work.Kernels.jInvariantFun (arcPt p₀.2)‖ := rfl
    have h2 : jarc (u, s)
        = ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun (arcPt s)‖ := rfl
    rw [h1, h2] at hmin
    exact hmin

/-! ## The master estimate on the compact core -/

/-- `‖u - i s‖ ≤ 1` for `|Re u| ≤ 1/2` and `|Im u - s| ≤ 13/20`. -/
lemma norm_sub_arc_le_one {u : ℍ} {s : ℝ} (hure : |u.re| ≤ 1 / 2)
    (huim : |u.im - s| ≤ 13 / 20) :
    ‖(u : ℂ) - Complex.I * (s : ℂ)‖ ≤ 1 := by
  have hz : ((u : ℂ) - Complex.I * (s : ℂ)).re = u.re := by simp
  have hi : ((u : ℂ) - Complex.I * (s : ℂ)).im = u.im - s := by
    simp [Complex.sub_im, Complex.mul_im]
  have hz1 : u.re ^ 2 ≤ 1 / 4 := by
    have h := abs_le.mp hure
    nlinarith [h.1, h.2]
  have hi1 : (u.im - s) ^ 2 ≤ 169 / 400 := by
    have h := abs_le.mp huim
    nlinarith [h.1, h.2]
  have hns : ‖(u : ℂ) - Complex.I * (s : ℂ)‖ ^ 2
      = u.re ^ 2 + (u.im - s) ^ 2 := by
    have h : ‖(u : ℂ) - Complex.I * (s : ℂ)‖ ^ 2
        = ((u : ℂ) - Complex.I * (s : ℂ)).re * ((u : ℂ) - Complex.I * (s : ℂ)).re
          + ((u : ℂ) - Complex.I * (s : ℂ)).im * ((u : ℂ) - Complex.I * (s : ℂ)).im := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    rw [h, hz, hi]; ring
  have hnn : 0 ≤ ‖(u : ℂ) - Complex.I * (s : ℂ)‖ := norm_nonneg _
  have h2 : ‖(u : ℂ) - Complex.I * (s : ℂ)‖ ^ 2 ≤ 1 := by linarith
  have h3 := (sq_le_one_iff_abs_le_one (‖(u : ℂ) - Complex.I * (s : ℂ)‖)).mp h2
  rwa [abs_of_nonneg hnn] at h3

/-- **The master bound on the box.**  For `u ∈ Jbox` and `s ∈ [37/20, 9/4]`,
`c ‖u - i s‖ ≤ ‖j u - j (i s)‖`. -/
theorem Jsmall :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℝ) (hs : 37 / 20 ≤ s) (hs2 : s ≤ 9 / 4) (u : ℍ),
      u ∈ Jbox →
      c * ‖(u : ℂ) - Complex.I * (s : ℂ)‖
        ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun (arcPt s)‖ := by
  obtain ⟨δ, c₁, hδ, hδhalf, hc₁, h₁⟩ := uniform_local_lower
  obtain ⟨c₂, hc₂, h₂⟩ := Jbox_norm_lower δ hδ hδhalf
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, ?_⟩
  intro s hs hs2 u hu
  have hmem := mem_Jbox.mp hu
  rcases le_or_gt δ ‖(u : ℂ) - Complex.I * (s : ℂ)‖ with hge | hlt
  · have hfar := h₂ s hs hs2 u hu hge
    have hure_abs : |u.re| ≤ 1 / 2 := by
      rw [abs_le]; exact ⟨by linarith [hmem.1.1], hmem.1.2⟩
    have huim_abs : |u.im - s| ≤ 13 / 20 := by
      rw [abs_le]; exact ⟨by linarith [hmem.2.1, hs2], by linarith [hmem.2.2, hs]⟩
    have hdist : ‖(u : ℂ) - Complex.I * (s : ℂ)‖ ≤ 1 :=
      norm_sub_arc_le_one hure_abs huim_abs
    calc min c₁ c₂ * ‖(u : ℂ) - Complex.I * (s : ℂ)‖
        ≤ c₂ * ‖(u : ℂ) - Complex.I * (s : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
      _ ≤ c₂ * 1 := mul_le_mul_of_nonneg_left hdist hc₂.le
      _ = c₂ := mul_one _
      _ ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun (arcPt s)‖ := hfar
  · have hnear : ‖((arcPt s : ℍ) : ℂ) - Complex.I * (s : ℂ)‖ < δ := by
      rw [arcPt_coe s (lt_of_lt_of_le (by norm_num) hs)]
      simpa using hδ
    have hloc := h₁ s hs hs2 u (arcPt s) hlt hnear
    rw [arcPt_coe s (lt_of_lt_of_le (by norm_num) hs)] at hloc
    calc min c₁ c₂ * ‖(u : ℂ) - Complex.I * (s : ℂ)‖
        ≤ c₁ * ‖(u : ℂ) - Complex.I * (s : ℂ)‖ :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
      _ ≤ ‖Work.Kernels.jInvariantFun u - Work.Kernels.jInvariantFun (arcPt s)‖ := hloc

/-! ## The target statement -/

theorem JLower :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℝ) (hs : 37 / 20 ≤ s) (τ : UpperHalfPlane),
      τ ∈ Work.Asymptotics.DomainD → |τ.im - s| ≤ 1 / 4 →
        c * Real.exp (2 * Real.pi * s) *
            (min (min ‖(τ : ℂ) - ((Work.Kernels.imagAxis s (by linarith) : UpperHalfPlane) : ℂ)‖
                    ‖(τ : ℂ) - ((((1 : ℝ) +ᵥ (Work.Kernels.imagAxis s (by linarith) : UpperHalfPlane)) : UpperHalfPlane) : ℂ)‖)
              ‖(τ : ℂ) - ((((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis s (by linarith) : UpperHalfPlane)) : UpperHalfPlane) : ℂ)‖)
          ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (1 / s) (by positivity))‖ := by
  obtain ⟨cB, hcB, hB⟩ := Work.Asymptotics.CuspDecay.j_sub_lower_lattice
  obtain ⟨cS, hcS, hSmall⟩ := Jsmall
  refine ⟨min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))), lt_min hcB (by positivity), ?_⟩
  intro s hs τ hτ him
  have hs0 : 0 < s := by linarith
  have hτre1 : -1 < τ.re := hτ.1
  have hτre2 : τ.re < 1 := hτ.2.1
  -- the nearest integer `k` to `τ.re`
  set k : ℤ := if (1 : ℝ) / 2 ≤ τ.re then 1 else if τ.re ≤ -(1 / 2) then -1 else 0 with hkdef
  have hk_cases : k = -1 ∨ k = 0 ∨ k = 1 := by
    rw [hkdef]
    split_ifs with h1 h2
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hkre : |τ.re - (k : ℝ)| ≤ 1 / 2 := by
    rw [hkdef]
    split_ifs with h1 h2
    · rw [abs_le]; constructor <;> push_cast <;> linarith
    · rw [abs_le]; constructor <;> push_cast <;> linarith
    · rw [abs_le]; constructor <;> push_cast <;> linarith
  -- the shifted point
  set u : ℍ := (-(k : ℝ)) +ᵥ τ with hu
  have hucoe : (u : ℂ) = (τ : ℂ) - (k : ℂ) := by
    rw [hu, UpperHalfPlane.coe_vadd]; push_cast; ring
  have hju : Work.Kernels.jInvariantFun u = Work.Kernels.jInvariantFun τ := by
    rw [hu]
    have := Work.Asymptotics.CuspDecay.jInvariantFun_vadd_int (-k) τ
    simpa using this
  have hure : -(1 : ℝ) / 2 ≤ u.re ∧ u.re ≤ 1 / 2 := by
    have h := abs_le.mp hkre
    rw [hu, UpperHalfPlane.vadd_re]
    constructor <;> push_cast <;> linarith
  have hure_abs : |u.re| ≤ 1 / 2 := by
    rw [abs_le]; exact ⟨by linarith [hure.1], hure.2⟩
  have huim_abs : |u.im - s| ≤ 1 / 4 := by
    rw [hu, UpperHalfPlane.vadd_im]; exact him
  -- the modular identifications
  have hσcoe : ((Work.Kernels.imagAxis s (by linarith) : ℍ) : ℂ) = Complex.I * (s : ℂ) := by
    show (s : ℂ) * Complex.I = Complex.I * (s : ℂ)
    exact mul_comm _ _
  have hRHS : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (1 / s) (by positivity))
      = Work.Kernels.jInvariantFun (arcPt s) := by
    rw [jInvariantFun_imagAxis_one_div s hs0, ← arcPt_eq_imagAxis s hs0]
  -- the min is at most the distance to the selected lattice point
  have hA : ‖(τ : ℂ) - ((Work.Kernels.imagAxis s (by linarith) : ℍ) : ℂ)‖
      = ‖(τ : ℂ) - (0 : ℂ) - Complex.I * (s : ℂ)‖ := by
    rw [hσcoe]; congr 1; ring
  have hB' : ‖(τ : ℂ) - ((((1 : ℝ) +ᵥ (Work.Kernels.imagAxis s (by linarith) : ℍ)) : ℍ) : ℂ)‖
      = ‖(τ : ℂ) - (1 : ℂ) - Complex.I * (s : ℂ)‖ := by
    rw [UpperHalfPlane.coe_vadd, hσcoe]; push_cast; congr 1; ring
  have hC' : ‖(τ : ℂ) - ((((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis s (by linarith) : ℍ)) : ℍ) : ℂ)‖
      = ‖(τ : ℂ) - (-(1 : ℂ)) - Complex.I * (s : ℂ)‖ := by
    rw [UpperHalfPlane.coe_vadd, hσcoe]; push_cast; congr 1; ring
  set m : ℝ := min (min ‖(τ : ℂ) - ((Work.Kernels.imagAxis s (by linarith) : ℍ) : ℂ)‖
        ‖(τ : ℂ) - ((((1 : ℝ) +ᵥ (Work.Kernels.imagAxis s (by linarith) : ℍ)) : ℍ) : ℂ)‖)
      ‖(τ : ℂ) - ((((-1 : ℝ) +ᵥ (Work.Kernels.imagAxis s (by linarith) : ℍ)) : ℍ) : ℂ)‖ with hm
  have hminnn : 0 ≤ m := by
    rw [hm]
    exact le_min (le_min (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hminW : m ≤ ‖(u : ℂ) - Complex.I * (s : ℂ)‖ := by
    rw [hm, hA, hB', hC', hucoe]
    rcases hk_cases with hk | hk | hk
    · rw [hk]; push_cast; exact min_le_right _ _
    · rw [hk]; push_cast; exact le_trans (min_le_left _ _) (min_le_left _ _)
    · rw [hk]; push_cast; exact le_trans (min_le_left _ _) (min_le_right _ _)
  rw [hRHS]
  by_cases hbig : (9 : ℝ) / 4 ≤ s
  · -- regime `s ≥ 9/4`
    have hτim2 : 2 ≤ τ.im := by linarith [(abs_le.mp him).1]
    have hσre : (Work.Kernels.imagAxis s (by linarith) : ℍ).re = 0 := by
      simp [Work.Kernels.imagAxis]
    have hσim : 2 ≤ (Work.Kernels.imagAxis s (by linarith) : ℍ).im := by
      simp [Work.Kernels.imagAxis]; linarith
    have hnorm1 : ‖(τ : ℂ) - ((Work.Kernels.imagAxis s (by linarith) : ℍ) : ℂ) - (k : ℂ)‖
        = ‖(u : ℂ) - Complex.I * (s : ℂ)‖ := by
      rw [hucoe, hσcoe]; congr 1; ring
    have hkn : ‖(τ : ℂ) - ((Work.Kernels.imagAxis s (by linarith) : ℍ) : ℂ) - (k : ℂ)‖ ≤ 2 := by
      rw [hnorm1]
      linarith [norm_sub_arc_le_one hure_abs (by
        rw [hu, UpperHalfPlane.vadd_im]
        exact le_trans him (by norm_num : (1 : ℝ) / 4 ≤ 13 / 20))]
    have hkey := hB τ (Work.Kernels.imagAxis s (by linarith)) k hσre hσim hτim2 hkre hkn
    have hq : ‖Work.Kernels.qParamFun (Work.Kernels.imagAxis s (by linarith))‖
        = Real.exp (-(2 * Real.pi * s)) := by
      rw [Work.Asymptotics.CuspDecay.norm_qParamFun_eq_exp]
      congr 1
      simp [Work.Kernels.imagAxis]
    have hdiv : ‖(u : ℂ) - Complex.I * (s : ℂ)‖ / Real.exp (-(2 * Real.pi * s))
        = Real.exp (2 * Real.pi * s) * ‖(u : ℂ) - Complex.I * (s : ℂ)‖ := by
      rw [Real.exp_neg, div_inv_eq_mul, mul_comm]
    have hjeq : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s (by linarith))
        = Work.Kernels.jInvariantFun (arcPt s) := (arcPt_eq_imagAxis s hs0).symm ▸ rfl
    have hstepB : cB * (Real.exp (2 * Real.pi * s) * ‖(u : ℂ) - Complex.I * (s : ℂ)‖)
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (arcPt s)‖ := by
      rw [← hjeq]
      calc cB * (Real.exp (2 * Real.pi * s) * ‖(u : ℂ) - Complex.I * (s : ℂ)‖)
          = cB * (‖(τ : ℂ) - ((Work.Kernels.imagAxis s (by linarith) : ℍ) : ℂ) - (k : ℂ)‖
              / ‖Work.Kernels.qParamFun (Work.Kernels.imagAxis s (by linarith))‖) := by
            rw [← hdiv, ← hnorm1, ← hq]
        _ ≤ ‖Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s (by linarith))‖ := hkey
    have hE' : Real.exp (2 * Real.pi * s) * m
        ≤ Real.exp (2 * Real.pi * s) * ‖(u : ℂ) - Complex.I * (s : ℂ)‖ :=
      mul_le_mul_of_nonneg_left hminW (Real.exp_pos _).le
    calc min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) * Real.exp (2 * Real.pi * s) * m
        = min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) *
            (Real.exp (2 * Real.pi * s) * m) := by ring
      _ ≤ cB * (Real.exp (2 * Real.pi * s) * ‖(u : ℂ) - Complex.I * (s : ℂ)‖) :=
          mul_le_mul (min_le_left _ _) hE'
            (mul_nonneg (Real.exp_pos _).le hminnn) hcB.le
      _ ≤ _ := hstepB
  · -- regime `s ≤ 9/4`
    have hs2 : s ≤ 9 / 4 := le_of_lt (not_le.mp hbig)
    have huim : (8 : ℝ) / 5 ≤ u.im ∧ u.im ≤ 5 / 2 := by
      have h := abs_le.mp him
      rw [hu, UpperHalfPlane.vadd_im]
      constructor <;> linarith
    have hJbox : u ∈ Jbox := mem_Jbox.mpr ⟨hure, huim⟩
    have hsmall := hSmall s hs hs2 u hJbox
    have hsmall' : cS * ‖(u : ℂ) - Complex.I * (s : ℂ)‖
        ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (arcPt s)‖ := by
      rw [← hju]
      exact hsmall
    have hE : Real.exp (2 * Real.pi * s) ≤ Real.exp (2 * Real.pi * (9 / 4)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hs2])
    have hcE : min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) * Real.exp (2 * Real.pi * s)
        ≤ cS := by
      have hc' : min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4))))
          ≤ cS * Real.exp (-(2 * Real.pi * (9 / 4))) := min_le_right _ _
      have hexp1 : Real.exp (-(2 * Real.pi * (9 / 4))) * Real.exp (2 * Real.pi * (9 / 4)) = 1 := by
        rw [← Real.exp_add]; norm_num
      calc min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) * Real.exp (2 * Real.pi * s)
          ≤ (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) * Real.exp (2 * Real.pi * (9 / 4)) :=
            mul_le_mul hc' hE (Real.exp_pos _).le (by positivity)
        _ = cS * (Real.exp (-(2 * Real.pi * (9 / 4))) * Real.exp (2 * Real.pi * (9 / 4))) := by ring
        _ = cS := by rw [hexp1, mul_one]
    calc min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) * Real.exp (2 * Real.pi * s) * m
        = (min cB (cS * Real.exp (-(2 * Real.pi * (9 / 4)))) * Real.exp (2 * Real.pi * s)) * m := by
          ring
      _ ≤ cS * ‖(u : ℂ) - Complex.I * (s : ℂ)‖ :=
          mul_le_mul hcE hminW hminnn hcS.le
      _ ≤ _ := hsmall'

end

end Work.Asymptotics.CuspDecay.KMinusMiddle

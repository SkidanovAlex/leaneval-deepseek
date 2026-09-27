import Mathlib
import Submission.Work.Drive.PushDisc.lensRegularDefs
import Submission.Work.Drive.PushDisc.lensBump_fderiv
import Submission.Work.Drive.PushDisc.lensBump_coeff_injective
import Submission.Work.Projection.dimH_image_le_of_contDiffOn
import Submission.Work.Drive.PushDisc.dimH_badColBot
import Submission.Work.Drive.PushDisc.dimH_badColTop

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff ENNReal
open Set Metric MeasureTheory Topology Filter

noncomputable section

/-! ## The parameter space of the lens perturbation

The perturbation `v` of `lensMap` ranges over `Prm n = (Fin 2 × Fin 2) → ℝ ^ (2n)`: one vector
per bump.  Its real dimension is `4 * (2n) = 8n`.  The four sets of "bad" parameters (where the
immersion, the injectivity or one of the two collar-transversality conditions fails) will be shown
to have Hausdorff dimension at most `7n + 1 < 8n`, so that a good parameter exists arbitrarily
close to `0`. -/

/-- The parameter space: one vector of `ℝ ^ (2n)` per bump. -/
abbrev Prm (n : ℕ) : Type := (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))

lemma finrank_prm (n : ℕ) : Module.finrank ℝ (Prm n) = 8 * n := by
  change Module.finrank ℝ ((Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n))) = 8 * n
  rw [Module.finrank_pi_fintype]
  simp only [finrank_euclideanSpace_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Fintype.card_prod, Fintype.card_fin]
  ring

/-! ## Derivatives with respect to the parameter -/

/-- `lensPert ρ v` is smooth. -/
lemma contDiff_lensPert {n : ℕ} (ρ : ℝ) (v : Prm n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lensPert ρ v) := by
  rw [show lensPert ρ v = (fun p : ℝ × ℝ => ∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k)
    from rfl]
  exact ContDiff.sum (s := Finset.univ) fun k _ => (contDiff_lensBump ρ k).smul_const (v k)

/-- The derivative of `lensPert ρ v` in the direction `u`. -/
lemma fderiv_lensPert_apply {n : ℕ} (ρ : ℝ) (v : Prm n) (p u : ℝ × ℝ) :
    fderiv ℝ (lensPert ρ v) p u
      = ∑ k : Fin 2 × Fin 2, (fderiv ℝ (lensBump ρ k) p u) • v k := by
  rw [show lensPert ρ v = (fun p : ℝ × ℝ => ∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k)
    from rfl]
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun k p => lensBump ρ k p • v k)
    (fun k _ => ((contDiff_lensBump ρ k).contDiffAt.differentiableAt (by simp)).smul_const
      (v k))]
  rw [sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [fderiv_smul_const ((contDiff_lensBump ρ k).contDiffAt.differentiableAt (by simp)) (v k)]
  rfl

/-- **The derivative of the perturbed lens map** in the direction `u`. -/
lemma fderiv_lensMap_apply {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ) (v : Prm n) (p u : ℝ × ℝ) :
    fderiv ℝ (lensMap Δ₀ ρ v) p u
      = fderiv ℝ Δ₀ p u + ∑ k : Fin 2 × Fin 2, (fderiv ℝ (lensBump ρ k) p u) • v k := by
  have hfun : lensMap Δ₀ ρ v = Δ₀ + lensPert ρ v := rfl
  rw [hfun, fderiv_add (hΔ₀.contDiffAt.differentiableAt (by simp))
    ((contDiff_lensPert ρ v).contDiffAt.differentiableAt (by simp)), add_apply,
    fderiv_lensPert_apply]

/-- A map on `ℝ × ℝ` is determined on the coordinate frame. -/
lemma fderiv_eq_pair_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : ℝ × ℝ → F) (p V : ℝ × ℝ) :
    fderiv ℝ g p V = V.1 • fderiv ℝ g p (1, 0) + V.2 • fderiv ℝ g p (0, 1) := by
  have hsplit : V = V.1 • (1, 0) + V.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [hsplit]
  rw [map_add, map_smul, map_smul]

/-! ## The bad parameter sets -/

/-- Parameters for which `lensMap` fails to be immersive on the lens. -/
def badImm {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) : Set (Prm n) :=
  {v | ∃ p ∈ lens, ¬ Function.Injective (fderiv ℝ (lensMap Δ₀ ρ v) p)}

/-- Parameters for which `lensMap` fails to be injective on the lens. -/
def badInj {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ) : Set (Prm n) :=
  {v | ∃ p ∈ lens, ∃ q ∈ lens, p ≠ q ∧ lensMap Δ₀ ρ v p = lensMap Δ₀ ρ v q}

/-! ## The vertical derivative of the bumps on the two edges -/

/-- The vertical derivative of a bump at the lower edge. -/
def edgeBot (ρ : ℝ) (k : Fin 2 × Fin 2) (x : ℝ) : ℝ :=
  fderiv ℝ (lensBump ρ k) (x, 0) (0, 1)

/-- The vertical derivative of a bump at the upper edge. -/
def edgeTop (ρ : ℝ) (k : Fin 2 × Fin 2) (x : ℝ) : ℝ :=
  fderiv ℝ (lensBump ρ k) (x, arch x) (0, 1)

lemma deriv_lensZeta_zero_bot (u : ℝ) :
    deriv (fun t : ℝ => lensZeta 0 t u) 0 = u := by
  have hfun : (fun t : ℝ => lensZeta 0 t u) = fun t : ℝ => u * t - t ^ 2 := by
    funext t; rw [lensZeta_zero_fun]; ring
  rw [hfun]
  change deriv ((fun t : ℝ => u * t) - fun t : ℝ => t ^ 2) 0 = u
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_const_mul_id, deriv_pow_field]
  norm_num

lemma deriv_lensZeta_zero_top (u : ℝ) :
    deriv (fun t : ℝ => lensZeta 0 t u) u = -u := by
  have hfun : (fun t : ℝ => lensZeta 0 t u) = fun t : ℝ => u * t - t ^ 2 := by
    funext t; rw [lensZeta_zero_fun]; ring
  rw [hfun]
  change deriv ((fun t : ℝ => u * t) - fun t : ℝ => t ^ 2) u = -u
  rw [deriv_sub (by fun_prop) (by fun_prop), deriv_const_mul_id, deriv_pow_field]
  ring

/-- **The vertical derivative of the `(0,0)`-bump at the lower edge is nonzero.** -/
lemma edgeBot_zero_ne {ρ x : ℝ} (hρ : 0 < ρ) (hx : |x| < 1) :
    edgeBot ρ (0, 0) x ≠ 0 := by
  have h := (lensBump_fderiv hρ (0, 0) (x, 0)).2
  rw [edgeBot, h, deriv_lensZeta_zero_bot]
  refine mul_ne_zero (mul_ne_zero (ne_of_gt (lensChi_pos_of_abs_lt_one hρ hx)) ?_) ?_
  · rw [lensAlpha_zero_fun]
    exact ne_of_gt (by rw [abs_lt] at hx; nlinarith [hx.1, hx.2])
  · exact ne_of_gt (arch_pos hx)

/-- **The vertical derivative of the `(0,0)`-bump at the upper edge is nonzero.** -/
lemma edgeTop_zero_ne {ρ x : ℝ} (hρ : 0 < ρ) (hx : |x| < 1) :
    edgeTop ρ (0, 0) x ≠ 0 := by
  have h := (lensBump_fderiv hρ (0, 0) (x, arch x)).2
  rw [edgeTop, h, deriv_lensZeta_zero_top]
  refine mul_ne_zero (mul_ne_zero (ne_of_gt (lensChi_pos_of_abs_lt_one hρ hx)) ?_) ?_
  · rw [lensAlpha_zero_fun]
    exact ne_of_gt (by rw [abs_lt] at hx; nlinarith [hx.1, hx.2])
  · exact neg_ne_zero.mpr (ne_of_gt (arch_pos hx))

/-- At every interior parameter there is a bump whose vertical derivative at the lower edge is
nonzero. -/
lemma exists_edgeBot_ne_zero {ρ x : ℝ} (hρ : 0 < ρ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ k : Fin 2 × Fin 2, edgeBot ρ k x ≠ 0 :=
  ⟨(0, 0), edgeBot_zero_ne hρ (abs_lt.mpr ⟨hx.1, hx.2⟩)⟩

/-- At every interior parameter there is a bump whose vertical derivative at the upper edge is
nonzero. -/
lemma exists_edgeTop_ne_zero {ρ x : ℝ} (hρ : 0 < ρ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    ∃ k : Fin 2 × Fin 2, edgeTop ρ k x ≠ 0 :=
  ⟨(0, 0), edgeTop_zero_ne hρ (abs_lt.mpr ⟨hx.1, hx.2⟩)⟩


/-! ## The index set with one bump removed -/

/-- The three bump indices different from `k₀`. -/
abbrev LensIdx (k₀ : Fin 2 × Fin 2) : Type := {k : Fin 2 × Fin 2 // k ≠ k₀}

lemma card_lensIdx (k₀ : Fin 2 × Fin 2) : Fintype.card (LensIdx k₀) = 3 := by
  obtain ⟨i, j⟩ := k₀
  fin_cases i <;> fin_cases j <;> decide

lemma finrank_free (n : ℕ) (k₀ : Fin 2 × Fin 2) :
    Module.finrank ℝ (LensIdx k₀ → EuclideanSpace ℝ (Fin (2 * n))) = 6 * n := by
  rw [Module.finrank_pi_fintype]
  simp only [finrank_euclideanSpace_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    card_lensIdx]
  ring

/-- Splitting a sum over the four bump indices at `k₀`. -/
lemma sum_split {E : Type*} [AddCommMonoid E] (k₀ : Fin 2 × Fin 2) (F : Fin 2 × Fin 2 → E) :
    (∑ k : Fin 2 × Fin 2, F k) = F k₀ + ∑ j : LensIdx k₀, F j.1 := by
  have herase : (∑ k ∈ (Finset.univ.erase k₀ : Finset (Fin 2 × Fin 2)), F k)
      = ∑ j : LensIdx k₀, F j.1 :=
    Finset.sum_subtype (p := fun k : Fin 2 × Fin 2 => k ≠ k₀) _ (fun x => by simp) F
  have hsplit : (∑ k : Fin 2 × Fin 2, F k)
      = (∑ k ∈ (Finset.univ.erase k₀ : Finset (Fin 2 × Fin 2)), F k) + F k₀ :=
    (Finset.sum_erase_add (Finset.univ) F (Finset.mem_univ k₀)).symm
  rw [hsplit, herase]
  exact add_comm _ _

/-- The source of the immersion- and injectivity-parametrisations attached to the index `k₀`:
a pair `(p, q)` of points of the plane together with the three blocks of `v` other than `k₀`. -/
abbrev ImmSrc (n : ℕ) (k₀ : Fin 2 × Fin 2) : Type :=
  (ℝ × ℝ) × (ℝ × ℝ) × (LensIdx k₀ → EuclideanSpace ℝ (Fin (2 * n)))

lemma finrank_immSrc (n : ℕ) (k₀ : Fin 2 × Fin 2) :
    Module.finrank ℝ (ImmSrc n k₀) = 6 * n + 4 := by
  simp only [ImmSrc, Module.finrank_prod, Module.finrank_self, Module.finrank_pi_fintype,
    finrank_euclideanSpace_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, card_lensIdx]
  ring

/-! ## Solving for one block of the parameter -/

/-- A linear map that is not injective kills a nonzero vector. -/
lemma exists_ker_dir_of_not_injective {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    {Λ : E →L[ℝ] F} (h : ¬ Function.Injective Λ) : ∃ u, u ≠ 0 ∧ Λ u = 0 := by
  rw [Function.Injective] at h
  push_neg at h
  obtain ⟨a, b, hab, hne⟩ := h
  exact ⟨a - b, sub_ne_zero.mpr hne, by rw [map_sub, hab, sub_self]⟩

/-- If an affine combination of the values of a parameter sums to zero, then the `k₀`-block is
determined by the other three blocks. -/
lemma smul_block_eq_of_sum_eq_zero {n : ℕ} (k₀ : Fin 2 × Fin 2) (d : Fin 2 × Fin 2 → ℝ)
    (v : Prm n) (A : EuclideanSpace ℝ (Fin (2 * n)))
    (h : A + ∑ k : Fin 2 × Fin 2, (d k) • v k = 0) :
    d k₀ • v k₀ = -(A + ∑ j : LensIdx k₀, (d j.1) • v j.1) := by
  have hsplit := sum_split k₀ (fun k : Fin 2 × Fin 2 => (d k) • v k)
  have h2 : A + ((d k₀) • v k₀ + ∑ j : LensIdx k₀, (d j.1) • v j.1) = 0 := by
    rw [← hsplit]; exact h
  have h3 : (A + ∑ j : LensIdx k₀, (d j.1) • v j.1) + (d k₀) • v k₀ = 0 := by
    simpa only [add_assoc, add_comm, add_left_comm] using h2
  exact eq_neg_of_add_eq_zero_right h3

/-- The algebraic content of the recovery of the `k₀`-block for the injectivity-bad set. -/
lemma smul_block_eq_of_lensMap_eq {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)))
    (ρ : ℝ) (k₀ : Fin 2 × Fin 2) (p q : ℝ × ℝ) (v : Prm n)
    (h : Δ₀ p + ∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k
       = Δ₀ q + ∑ k : Fin 2 × Fin 2, lensBump ρ k q • v k) :
    (lensBump ρ k₀ p - lensBump ρ k₀ q) • v k₀
      = (Δ₀ q - Δ₀ p) + ∑ j : LensIdx k₀, (lensBump ρ j.1 q - lensBump ρ j.1 p) • v j.1 := by
  have h1 : ∑ k : Fin 2 × Fin 2, (lensBump ρ k p - lensBump ρ k q) • v k
      = Δ₀ q - Δ₀ p := by
    have hsub : ∑ k : Fin 2 × Fin 2, (lensBump ρ k p - lensBump ρ k q) • v k
        = ∑ k, (lensBump ρ k p) • v k - ∑ k, (lensBump ρ k q) • v k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [sub_smul]
    rw [hsub]
    have hh : (Δ₀ p + ∑ k, (lensBump ρ k p) • v k)
        - (Δ₀ q + ∑ k, (lensBump ρ k q) • v k) = 0 := by rw [h, sub_self]
    have e : (Δ₀ p + ∑ k, (lensBump ρ k p) • v k)
        - (Δ₀ q + ∑ k, (lensBump ρ k q) • v k)
        = ((∑ k, (lensBump ρ k p) • v k) - ∑ k, (lensBump ρ k q) • v k)
          - (Δ₀ q - Δ₀ p) := by abel
    rw [e] at hh
    exact sub_eq_zero.mp hh
  have h2 : ∑ k : Fin 2 × Fin 2, (lensBump ρ k p - lensBump ρ k q) • v k
      = (lensBump ρ k₀ p - lensBump ρ k₀ q) • v k₀
        + ∑ j : LensIdx k₀, (lensBump ρ j.1 p - lensBump ρ j.1 q) • v j.1 :=
    sum_split k₀ _
  have h3 : ∑ j : LensIdx k₀, (lensBump ρ j.1 q - lensBump ρ j.1 p) • v j.1
      = -∑ j : LensIdx k₀, (lensBump ρ j.1 p - lensBump ρ j.1 q) • v j.1 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [← neg_sub, neg_smul]
  have hmain : (lensBump ρ k₀ p - lensBump ρ k₀ q) • v k₀
      + (∑ j : LensIdx k₀, (lensBump ρ j.1 p - lensBump ρ j.1 q) • v j.1)
      = Δ₀ q - Δ₀ p := by rw [← h2, h1]
  rw [h3]
  have hgoal : (lensBump ρ k₀ p - lensBump ρ k₀ q) • v k₀
      = (Δ₀ q - Δ₀ p)
        - ∑ j : LensIdx k₀, (lensBump ρ j.1 p - lensBump ρ j.1 q) • v j.1 :=
    (eq_sub_iff_add_eq).mpr hmain
  rw [hgoal, sub_eq_add_neg]

/-! ## The immersion parametrisation -/


/-! ## Smoothness helpers on the parametrising spaces -/

lemma contDiffOn_src_fst {n : ℕ} (k₀ : Fin 2 × Fin 2) (s : Set (ImmSrc n k₀)) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => q.1) s := by fun_prop

lemma contDiffOn_src_snd_fst {n : ℕ} (k₀ : Fin 2 × Fin 2) (s : Set (ImmSrc n k₀)) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => q.2.1) s := by fun_prop

lemma contDiffOn_src_free {n : ℕ} (k₀ : Fin 2 × Fin 2) (s : Set (ImmSrc n k₀))
    (j : LensIdx k₀) : ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => q.2.2 j) s := by fun_prop

lemma contDiffOn_lensBump_fst {n : ℕ} (ρ : ℝ) (k k₀ : Fin 2 × Fin 2)
    (s : Set (ImmSrc n k₀)) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => lensBump ρ k q.1) s :=
  ((contDiff_lensBump ρ k).of_le (by simp)).comp_contDiffOn (contDiffOn_src_fst k₀ s)

lemma contDiffOn_lensBump_snd {n : ℕ} (ρ : ℝ) (k k₀ : Fin 2 × Fin 2)
    (s : Set (ImmSrc n k₀)) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => lensBump ρ k q.2.1) s :=
  ((contDiff_lensBump ρ k).of_le (by simp)).comp_contDiffOn (contDiffOn_src_snd_fst k₀ s)

lemma contDiffOn_base_fst {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (k₀ : Fin 2 × Fin 2)
    (s : Set (ImmSrc n k₀)) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => Δ₀ q.1) s :=
  (hΔ₀.of_le (by simp)).comp_contDiffOn (contDiffOn_src_fst k₀ s)

lemma contDiffOn_base_snd {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (k₀ : Fin 2 × Fin 2)
    (s : Set (ImmSrc n k₀)) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => Δ₀ q.2.1) s :=
  (hΔ₀.of_le (by simp)).comp_contDiffOn (contDiffOn_src_snd_fst k₀ s)

/-- The immersion parametrisation: the `k₀`-block is recovered from `p`, the direction `u` and the
three other blocks, using that `fderiv (lensBump ρ k₀) p u ≠ 0` on the domain. -/
def immParam {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (k₀ : Fin 2 × Fin 2) (q : ImmSrc n k₀) : Prm n :=
  fun k => if h : k = k₀ then
      ((fderiv ℝ (lensBump ρ k₀) q.1 q.2.1)⁻¹) •
        (-(fderiv ℝ Δ₀ q.1 q.2.1 + ∑ j : LensIdx k₀,
            (fderiv ℝ (lensBump ρ j.1) q.1 q.2.1) • q.2.2 j))
    else q.2.2 ⟨k, h⟩

/-- The open domain of the immersion parametrisation. -/
def immDom {n : ℕ} (ρ : ℝ) (k₀ : Fin 2 × Fin 2) : Set (ImmSrc n k₀) :=
  {q | fderiv ℝ (lensBump ρ k₀) q.1 q.2.1 ≠ 0}

lemma immParam_same {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (k₀ : Fin 2 × Fin 2) (q : ImmSrc n k₀) :
    immParam Δ₀ ρ k₀ q k₀ =
      ((fderiv ℝ (lensBump ρ k₀) q.1 q.2.1)⁻¹) •
        (-(fderiv ℝ Δ₀ q.1 q.2.1 + ∑ j : LensIdx k₀,
            (fderiv ℝ (lensBump ρ j.1) q.1 q.2.1) • q.2.2 j)) := by
  rw [immParam]; simp

lemma immParam_ne {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (k₀ : Fin 2 × Fin 2) (q : ImmSrc n k₀) {k : Fin 2 × Fin 2} (hk : k ≠ k₀) :
    immParam Δ₀ ρ k₀ q k = q.2.2 ⟨k, hk⟩ := by
  rw [immParam]; simp [hk]

lemma isOpen_immDom {n : ℕ} (ρ : ℝ) (k₀ : Fin 2 × Fin 2) : IsOpen (immDom (n := n) ρ k₀) := by
  have hcont : Continuous (fun q : ImmSrc n k₀ => fderiv ℝ (lensBump ρ k₀) q.1 q.2.1) :=
    (((contDiff_infty_iff_fderiv.mp (contDiff_lensBump ρ k₀)).2.continuous.comp
      continuous_fst)).clm_apply (continuous_fst.comp continuous_snd)
  show IsOpen {q : ImmSrc n k₀ | fderiv ℝ (lensBump ρ k₀) q.1 q.2.1 ≠ 0}
  exact isOpen_ne.preimage hcont

lemma contDiffOn_fderiv_lensBump_comp {n : ℕ} (ρ : ℝ) (k k₀ : Fin 2 × Fin 2) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => fderiv ℝ (lensBump ρ k) q.1 q.2.1)
      (immDom ρ k₀) := by
  have hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ (lensBump ρ k) p) :=
    ((contDiff_infty_iff_fderiv.mp (contDiff_lensBump ρ k)).2).of_le (by simp)
  have h1 : ContDiffOn ℝ 1
      (fun q : ImmSrc n k₀ => fderiv ℝ (lensBump ρ k) q.1) (immDom ρ k₀) :=
    hF.comp_contDiffOn contDiffOn_fst
  exact h1.clm_apply (by fun_prop)

lemma contDiffOn_fderiv_base_comp {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ) (k₀ : Fin 2 × Fin 2) :
    ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => fderiv ℝ Δ₀ q.1 q.2.1) (immDom ρ k₀) := by
  have hF : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ Δ₀ p) :=
    ((contDiff_infty_iff_fderiv.mp hΔ₀).2).of_le (by simp)
  have h1 : ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => fderiv ℝ Δ₀ q.1) (immDom ρ k₀) :=
    hF.comp_contDiffOn contDiffOn_fst
  exact h1.clm_apply (by fun_prop)

lemma contDiffOn_immParam {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ) (k₀ : Fin 2 × Fin 2) :
    ContDiffOn ℝ 1 (immParam Δ₀ ρ k₀) (immDom ρ k₀) := by
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = k₀
  · have hfun : (fun q : ImmSrc n k₀ => immParam Δ₀ ρ k₀ q k) =
        fun q : ImmSrc n k₀ =>
          ((fderiv ℝ (lensBump ρ k₀) q.1 q.2.1)⁻¹) •
            (-(fderiv ℝ Δ₀ q.1 q.2.1 + ∑ j : LensIdx k₀,
                (fderiv ℝ (lensBump ρ j.1) q.1 q.2.1) • q.2.2 j)) := by
      funext q
      rw [immParam]; simp [hk]
    rw [hfun]
    have h1 : ContDiffOn ℝ 1
        (fun q : ImmSrc n k₀ => (fderiv ℝ (lensBump ρ k₀) q.1 q.2.1)⁻¹) (immDom ρ k₀) :=
      (contDiffOn_fderiv_lensBump_comp ρ k₀ k₀).inv (fun q hq => hq)
    have h2 : ContDiffOn ℝ 1
        (fun q : ImmSrc n k₀ =>
          -(fderiv ℝ Δ₀ q.1 q.2.1 + ∑ j : LensIdx k₀,
            (fderiv ℝ (lensBump ρ j.1) q.1 q.2.1) • q.2.2 j)) (immDom ρ k₀) := by
      refine ContDiffOn.neg ?_
      refine ContDiffOn.add (contDiffOn_fderiv_base_comp hΔ₀ ρ k₀) ?_
      refine ContDiffOn.sum (s := Finset.univ) fun j _ => ?_
      have hb : ContDiffOn ℝ 1
          (fun q : ImmSrc n k₀ => fderiv ℝ (lensBump ρ j.1) q.1 q.2.1) (immDom ρ k₀) :=
        contDiffOn_fderiv_lensBump_comp ρ j.1 k₀
      have hb2 : ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => q.2.2 j) (immDom ρ k₀) :=
        contDiffOn_src_free k₀ _ j
      exact hb.smul hb2
    exact h1.smul h2
  · have hfun : (fun q : ImmSrc n k₀ => immParam Δ₀ ρ k₀ q k) =
        fun q : ImmSrc n k₀ => q.2.2 ⟨k, hk⟩ := by
      funext q
      rw [immParam]; simp [hk]
    rw [hfun]
    fun_prop

/-- **Every immersion-bad parameter occurs as a value of one of the four immersivity
parametrisations.** -/
lemma badImm_subset_iUnion {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {ρ : ℝ}
    (hbaseImm : ∀ p ∈ lens, ∀ UW : ℝ × ℝ, UW ≠ 0 →
      (∀ k : Fin 2 × Fin 2, UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0)
          + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1) = 0) →
      UW.1 • (fderiv ℝ Δ₀ p) (1, 0) + UW.2 • (fderiv ℝ Δ₀ p) (0, 1) ≠ 0)
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) :
    badImm Δ₀ ρ ⊆ ⋃ k₀ : Fin 2 × Fin 2, immParam Δ₀ ρ k₀ '' immDom ρ k₀ := by
  rintro v ⟨p, hp, hninj⟩
  obtain ⟨u, hu0, hukill⟩ := exists_ker_dir_of_not_injective hninj
  rw [fderiv_lensMap_apply hΔ₀ ρ v p u] at hukill
  rcases em (∃ k₀, fderiv ℝ (lensBump ρ k₀) p u ≠ 0) with ⟨k₀, hk₀⟩ | hnone
  · refine Set.mem_iUnion.mpr ⟨k₀, ⟨⟨p, u, fun j => v j.1⟩, hk₀, ?_⟩⟩
    funext k
    by_cases hkk : k = k₀
    · rw [hkk, immParam_same, inv_smul_eq_iff₀ hk₀]
      exact (smul_block_eq_of_sum_eq_zero k₀ (fun k => fderiv ℝ (lensBump ρ k) p u) v
        (fderiv ℝ Δ₀ p u) hukill).symm
    · rw [immParam_ne Δ₀ ρ k₀ _ hkk]
  · push_neg at hnone
    have hu0' : fderiv ℝ Δ₀ p u = 0 := by
      have hz : (∑ k : Fin 2 × Fin 2, (fderiv ℝ (lensBump ρ k) p u) • v k) = 0 := by
        simp only [hnone, zero_smul, Finset.sum_const_zero]
      rw [hz, add_zero] at hukill
      exact hukill
    have hprem : ∀ k : Fin 2 × Fin 2, u.1 * fderiv ℝ (lensBump ρ k) p (1, 0)
        + u.2 * fderiv ℝ (lensBump ρ k) p (0, 1) = 0 := by
      intro k
      rw [← fderiv_eq_pair (lensBump ρ k) p u, hnone k]
    have hconcl := hbaseImm p hp u hu0 hprem
    rw [fderiv_eq_pair_smul] at hu0'
    exact absurd hu0' hconcl

lemma dimH_badImm_le {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {ρ : ℝ}
    (hbaseImm : ∀ p ∈ lens, ∀ UW : ℝ × ℝ, UW ≠ 0 →
      (∀ k : Fin 2 × Fin 2, UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0)
          + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1) = 0) →
      UW.1 • (fderiv ℝ Δ₀ p) (1, 0) + UW.2 • (fderiv ℝ Δ₀ p) (0, 1) ≠ 0)
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) :
    dimH (badImm Δ₀ ρ) ≤ ((6 * n + 4 : ℕ) : ENNReal) := by
  calc dimH (badImm Δ₀ ρ)
      ≤ dimH (⋃ k₀ : Fin 2 × Fin 2, immParam Δ₀ ρ k₀ '' immDom ρ k₀) :=
        dimH_mono (badImm_subset_iUnion hbaseImm hΔ₀)
    _ = ⨆ k₀ : Fin 2 × Fin 2, dimH (immParam Δ₀ ρ k₀ '' immDom ρ k₀) := dimH_iUnion _
    _ ≤ ((6 * n + 4 : ℕ) : ENNReal) := by
        refine iSup_le fun k₀ => ?_
        calc dimH (immParam Δ₀ ρ k₀ '' immDom ρ k₀)
            ≤ (Module.finrank ℝ (ImmSrc n k₀) : ENNReal) :=
              Work.Projection.dimH_image_le_of_contDiffOn (isOpen_immDom ρ k₀)
                (contDiffOn_immParam hΔ₀ ρ k₀) Set.Subset.rfl
          _ = ((6 * n + 4 : ℕ) : ENNReal) := by rw [finrank_immSrc]

/-! ## The injectivity parametrisation -/

/-- The injectivity parametrisation: the `k₀`-block is recovered from the pair `(p, q)` and the
three other blocks, using that `lensBump ρ k₀ p ≠ lensBump ρ k₀ q` on the domain. -/
def injParam {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (k₀ : Fin 2 × Fin 2) (q : ImmSrc n k₀) : Prm n :=
  fun k => if h : k = k₀ then
      (lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1)⁻¹ •
        ((Δ₀ q.2.1 - Δ₀ q.1) + ∑ j : LensIdx k₀,
          (lensBump ρ j.1 q.2.1 - lensBump ρ j.1 q.1) • q.2.2 j)
    else q.2.2 ⟨k, h⟩

/-- The open domain of the injectivity parametrisation. -/
def injDom {n : ℕ} (ρ : ℝ) (k₀ : Fin 2 × Fin 2) : Set (ImmSrc n k₀) :=
  {q | lensBump ρ k₀ q.1 ≠ lensBump ρ k₀ q.2.1}

lemma injParam_same {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (k₀ : Fin 2 × Fin 2) (q : ImmSrc n k₀) :
    injParam Δ₀ ρ k₀ q k₀ =
      (lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1)⁻¹ •
        ((Δ₀ q.2.1 - Δ₀ q.1) + ∑ j : LensIdx k₀,
          (lensBump ρ j.1 q.2.1 - lensBump ρ j.1 q.1) • q.2.2 j) := by
  rw [injParam]; simp

lemma injParam_ne {n : ℕ} (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (ρ : ℝ)
    (k₀ : Fin 2 × Fin 2) (q : ImmSrc n k₀) {k : Fin 2 × Fin 2} (hk : k ≠ k₀) :
    injParam Δ₀ ρ k₀ q k = q.2.2 ⟨k, hk⟩ := by
  rw [injParam]; simp [hk]

lemma isOpen_injDom {n : ℕ} (ρ : ℝ) (k₀ : Fin 2 × Fin 2) : IsOpen (injDom (n := n) ρ k₀) := by
  have hcont : Continuous (fun q : ImmSrc n k₀ => lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1) :=
    ((contDiff_lensBump ρ k₀).continuous.comp continuous_fst).sub
      ((contDiff_lensBump ρ k₀).continuous.comp (continuous_fst.comp continuous_snd))
  have hset : injDom (n := n) ρ k₀ =
      {q : ImmSrc n k₀ | lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1 ≠ 0} := by
    ext q; simp [injDom, sub_ne_zero]
  rw [hset]
  exact isOpen_ne.preimage hcont

lemma contDiffOn_injParam {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))}
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) (ρ : ℝ) (k₀ : Fin 2 × Fin 2) :
    ContDiffOn ℝ 1 (injParam Δ₀ ρ k₀) (injDom ρ k₀) := by
  rw [contDiffOn_pi]
  intro k
  by_cases hk : k = k₀
  · have hfun : (fun q : ImmSrc n k₀ => injParam Δ₀ ρ k₀ q k) =
        fun q : ImmSrc n k₀ =>
          (lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1)⁻¹ •
            ((Δ₀ q.2.1 - Δ₀ q.1) + ∑ j : LensIdx k₀,
              (lensBump ρ j.1 q.2.1 - lensBump ρ j.1 q.1) • q.2.2 j) := by
      funext q
      rw [injParam]; simp [hk]
    rw [hfun]
    have hden : ContDiffOn ℝ 1
        (fun q : ImmSrc n k₀ => lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1) (injDom ρ k₀) :=
      (contDiffOn_lensBump_fst ρ k₀ k₀ _).sub (contDiffOn_lensBump_snd ρ k₀ k₀ _)
    have hinv : ContDiffOn ℝ 1
        (fun q : ImmSrc n k₀ => (lensBump ρ k₀ q.1 - lensBump ρ k₀ q.2.1)⁻¹) (injDom ρ k₀) :=
      hden.inv (fun q hq => sub_ne_zero.mpr hq)
    have hrest : ContDiffOn ℝ 1
        (fun q : ImmSrc n k₀ =>
          (Δ₀ q.2.1 - Δ₀ q.1) + ∑ j : LensIdx k₀,
            (lensBump ρ j.1 q.2.1 - lensBump ρ j.1 q.1) • q.2.2 j) (injDom ρ k₀) := by
      refine ContDiffOn.add
        ((contDiffOn_base_snd hΔ₀ k₀ _).sub (contDiffOn_base_fst hΔ₀ k₀ _)) ?_
      refine ContDiffOn.sum (s := Finset.univ) fun j _ => ?_
      have hb : ContDiffOn ℝ 1
          (fun q : ImmSrc n k₀ => lensBump ρ j.1 q.2.1 - lensBump ρ j.1 q.1) (injDom ρ k₀) :=
        (contDiffOn_lensBump_snd ρ j.1 k₀ _).sub (contDiffOn_lensBump_fst ρ j.1 k₀ _)
      have hb2 : ContDiffOn ℝ 1 (fun q : ImmSrc n k₀ => q.2.2 j) (injDom ρ k₀) :=
        contDiffOn_src_free k₀ _ j
      exact hb.smul hb2
    exact hinv.smul hrest
  · have hfun : (fun q : ImmSrc n k₀ => injParam Δ₀ ρ k₀ q k) =
        fun q : ImmSrc n k₀ => q.2.2 ⟨k, hk⟩ := by
      funext q
      rw [injParam]; simp [hk]
    rw [hfun]
    fun_prop

/-- **Every injectivity-bad parameter occurs as a value of one of the four injectivity
parametrisations.** -/
lemma badInj_subset_iUnion {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {ρ : ℝ}
    (hbaseInj : ∀ p ∈ lens, ∀ q ∈ lens, p ≠ q →
      (∀ k : Fin 2 × Fin 2, lensBump ρ k p = lensBump ρ k q) → Δ₀ p ≠ Δ₀ q) :
    badInj Δ₀ ρ ⊆ ⋃ k₀ : Fin 2 × Fin 2, injParam Δ₀ ρ k₀ '' injDom ρ k₀ := by
  rintro v ⟨p, hp, q, hq, hpq, heq⟩
  rcases em (∃ k₀, lensBump ρ k₀ p ≠ lensBump ρ k₀ q) with ⟨k₀, hk₀⟩ | hnone
  · refine Set.mem_iUnion.mpr ⟨k₀, ⟨⟨p, q, fun j => v j.1⟩, hk₀, ?_⟩⟩
    funext k
    by_cases hkk : k = k₀
    · rw [hkk, injParam_same, inv_smul_eq_iff₀ (sub_ne_zero.mpr hk₀)]
      exact (smul_block_eq_of_lensMap_eq Δ₀ ρ k₀ p q v (by simpa only [lensMap, lensPert] using heq)).symm
    · rw [injParam_ne Δ₀ ρ k₀ _ hkk]
  · push_neg at hnone
    have hΔ : Δ₀ p = Δ₀ q := by
      have hsum : (∑ k : Fin 2 × Fin 2, lensBump ρ k p • v k)
          = ∑ k : Fin 2 × Fin 2, lensBump ρ k q • v k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hnone k]
      have h2 : Δ₀ p + ∑ k, lensBump ρ k p • v k = Δ₀ q + ∑ k, lensBump ρ k q • v k :=
        by simpa only [lensMap, lensPert] using heq
      rw [hsum] at h2
      exact add_right_cancel h2
    exact absurd hΔ (hbaseInj p hp q hq hpq hnone)

lemma dimH_badInj_le {n : ℕ} {Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))} {ρ : ℝ}
    (hbaseInj : ∀ p ∈ lens, ∀ q ∈ lens, p ≠ q →
      (∀ k : Fin 2 × Fin 2, lensBump ρ k p = lensBump ρ k q) → Δ₀ p ≠ Δ₀ q)
    (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀) :
    dimH (badInj Δ₀ ρ) ≤ ((6 * n + 4 : ℕ) : ENNReal) := by
  calc dimH (badInj Δ₀ ρ)
      ≤ dimH (⋃ k₀ : Fin 2 × Fin 2, injParam Δ₀ ρ k₀ '' injDom ρ k₀) :=
        dimH_mono (badInj_subset_iUnion hbaseInj)
    _ = ⨆ k₀ : Fin 2 × Fin 2, dimH (injParam Δ₀ ρ k₀ '' injDom ρ k₀) := dimH_iUnion _
    _ ≤ ((6 * n + 4 : ℕ) : ENNReal) := by
        refine iSup_le fun k₀ => ?_
        calc dimH (injParam Δ₀ ρ k₀ '' injDom ρ k₀)
            ≤ (Module.finrank ℝ (ImmSrc n k₀) : ENNReal) :=
              Work.Projection.dimH_image_le_of_contDiffOn (isOpen_injDom ρ k₀)
                (contDiffOn_injParam hΔ₀ ρ k₀) Set.Subset.rfl
          _ = ((6 * n + 4 : ℕ) : ENNReal) := by rw [finrank_immSrc]
end

theorem exists_goodLensParam {n : ℕ} (hn : 3 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y : M, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (γ₁ γ₂ : ℝ → M)
    (hγ₁ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂ : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (ρ : ℝ) (hρ : 0 < ρ)
    (Δ₀ : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n))) (hΔ₀ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Δ₀)
    (hbaseInj : ∀ p ∈ lens, ∀ q ∈ lens, p ≠ q →
      (∀ k : Fin 2 × Fin 2, lensBump ρ k p = lensBump ρ k q) → Δ₀ p ≠ Δ₀ q)
    (hbaseImm : ∀ p ∈ lens, ∀ UW : ℝ × ℝ, UW ≠ 0 →
      (∀ k : Fin 2 × Fin 2,
        UW.1 * fderiv ℝ (lensBump ρ k) p (1, 0) + UW.2 * fderiv ℝ (lensBump ρ k) p (0, 1) = 0) →
      UW.1 • (fderiv ℝ Δ₀ p) (1, 0) + UW.2 • (fderiv ℝ Δ₀ p) (0, 1) ≠ 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ v : (Fin 2 × Fin 2) → EuclideanSpace ℝ (Fin (2 * n)),
      (∀ k : Fin 2 × Fin 2, ‖v k‖ < r) ∧
      (∀ p ∈ lens, Function.Injective (fderiv ℝ (lensMap Δ₀ ρ v) p)) ∧
      Set.InjOn (lensMap Δ₀ ρ v) lens ∧
      (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        fderiv ℝ (lensMap Δ₀ ρ v) (x, 0) (0, 1) ∉
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₁ (Work.Drive.Whitney.sigR x))).range) ∧
      (∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        fderiv ℝ (lensMap Δ₀ ρ v) (x, arch x) (0, 1) ∉
          (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f (γ₂ (Work.Drive.Whitney.sigR x))).range) := by
  have _hM : Nonempty M := ⟨γ₁ 0⟩
  -- the four bad parameter sets
  have h1 : dimH (badImm Δ₀ ρ) ≤ ((6 * n + 4 : ℕ) : ENNReal) := dimH_badImm_le hbaseImm hΔ₀
  have h2 : dimH (badInj Δ₀ ρ) ≤ ((6 * n + 4 : ℕ) : ENNReal) := dimH_badInj_le hbaseInj hΔ₀
  have h3 : dimH (badColBot f Δ₀ ρ γ₁) ≤ ((7 * n + 1 : ℕ) : ENNReal) :=
    dimH_badColBot f hf γ₁ hγ₁ Δ₀ hΔ₀ ρ hρ
  have h4 : dimH (badColTop f Δ₀ ρ γ₂) ≤ ((7 * n + 1 : ℕ) : ENNReal) :=
    dimH_badColTop f hf γ₂ hγ₂ Δ₀ hΔ₀ ρ hρ
  set Bad : Set (Prm n) := badImm Δ₀ ρ ∪ badInj Δ₀ ρ ∪ badColBot f Δ₀ ρ γ₁ ∪ badColTop f Δ₀ ρ γ₂
    with hBad
  have h64 : ((6 * n + 4 : ℕ) : ENNReal) ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
    rw [Nat.cast_le]; omega
  have hdim : dimH Bad ≤ ((7 * n + 1 : ℕ) : ENNReal) := by
    rw [hBad]
    rw [dimH_union, dimH_union, dimH_union]
    exact max_le (max_le (max_le (h1.trans h64) (h2.trans h64)) h3) h4
  have hlt : dimH Bad < (Module.finrank ℝ (Prm n) : ENNReal) := by
    rw [finrank_prm]
    exact lt_of_le_of_lt hdim (by rw [Nat.cast_lt]; omega)
  have hUopen : IsOpen {v : Prm n | ∀ k : Fin 2 × Fin 2, ‖v k‖ < r} := by
    rw [show {v : Prm n | ∀ k : Fin 2 × Fin 2, ‖v k‖ < r}
        = ⋂ k : Fin 2 × Fin 2, {v : Prm n | ‖v k‖ < r} from by
      ext v; simp]
    exact isOpen_iInter_of_finite fun k =>
      isOpen_lt (continuous_norm.comp (continuous_apply k)) continuous_const
  have hUne : ({v : Prm n | ∀ k : Fin 2 × Fin 2, ‖v k‖ < r}).Nonempty :=
    ⟨0, fun k => by simpa using hr⟩
  obtain ⟨v, hvBad, hvball⟩ :=
    (dense_compl_of_dimH_lt_finrank hlt).exists_mem_open hUopen hUne
  have hv1 : v ∉ badImm Δ₀ ρ := fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inl (Or.inl h)))
  have hv2 : v ∉ badInj Δ₀ ρ := fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inl (Or.inr h)))
  have hv3 : v ∉ badColBot f Δ₀ ρ γ₁ := fun h => hvBad (by rw [hBad]; exact Or.inl (Or.inr h))
  have hv4 : v ∉ badColTop f Δ₀ ρ γ₂ := fun h => hvBad (by rw [hBad]; exact Or.inr h)
  refine ⟨v, hvball, ?_, ?_, ?_, ?_⟩
  · intro p hp
    by_contra hinj
    exact hv1 ⟨p, hp, hinj⟩
  · intro p hp q hq hpq
    by_contra hne
    exact hv2 ⟨p, hp, q, hq, hne, hpq⟩
  · intro x hx
    by_contra hmem
    exact hv3 ⟨x, hx, hmem⟩
  · intro x hx
    by_contra hmem
    exact hv4 ⟨x, hx, hmem⟩

end Work.Drive.PushDisc

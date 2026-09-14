import Mathlib
import ChallengeDeps
import Submission.Voronoi
import Submission.GaussianMeasure
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq

open Module MeasureTheory Metric
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false

/-! Voronoi cell is a fundamental domain + Lemma rho_gamma (CDLP). -/

namespace Submission.VoronoiMeasure

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "VC" => Submission.Voronoi.voronoi

/-- Norm form of Voronoi-cell membership. -/
lemma mem_voronoi_iff_norm {ℒ : Submodule ℤ E} (x : E) :
    x ∈ VC ℒ ↔ ∀ w : ℒ, ‖x‖ ^ 2 ≤ ‖x - (w : E)‖ ^ 2 := by
  rw [Submission.Voronoi.mem_voronoi]
  constructor
  · intro h w
    have hw := h w
    have hnorm : ‖x - (w : E)‖ ^ 2 = ‖x‖ ^ 2 + ‖(w : E)‖ ^ 2 - 2 * ⟪x, (w : E)⟫_ℝ := by
      rw [norm_sub_sq_real]
      ring
    rw [hnorm]
    nlinarith
  · intro h w
    have hw := h w
    have hnorm : ‖x - (w : E)‖ ^ 2 = ‖x‖ ^ 2 + ‖(w : E)‖ ^ 2 - 2 * ⟪x, (w : E)⟫_ℝ := by
      rw [norm_sub_sq_real]
      ring
    nlinarith

/-- A translate cell `y + V` as a membership test. -/
lemma mem_cell_iff {ℒ : Submodule ℤ E} (y : ℒ) (x : E) :
    x ∈ ((y : E) +ᵥ VC ℒ) ↔ x - (y : E) ∈ VC ℒ := by
  constructor
  · rw [Set.mem_vadd_set]
    rintro ⟨a, ha, hx⟩
    have hEq : ((y : E) +ᵥ a) - (y : E) = a := by
      change ((y : E) + a) - (y : E) = a
      abel
    rwa [← hx, hEq]
  · intro h
    rw [Set.mem_vadd_set]
    exact ⟨x - (y : E), h, by
      change (y : E) + (x - (y : E)) = x
      abel⟩

/-- If `x − y ∈ V(ℒ)` then `y` is a nearest lattice point to `x`. -/
lemma nearest_of_vadd_mem {ℒ : Submodule ℤ E} (y : ℒ) (x : E) (h : x - (y : E) ∈ VC ℒ) :
    ∀ z : ℒ, ‖x - (y : E)‖ ≤ ‖x - (z : E)‖ := by
  intro z
  have hz := (mem_voronoi_iff_norm (ℒ := ℒ) (x - (y : E))).mp h (z - y)
  calc
    ‖x - (y : E)‖ ≤ ‖(x - (y : E)) - ((z - y : ℒ) : E)‖ := le_of_sq_le_sq hz (norm_nonneg _)
    _ = ‖x - (z : E)‖ := by
      congr 1
      simp only [Submodule.coe_sub]
      abel

/-- If `y` is a nearest lattice point then `(−y) + x ∈ V(ℒ)` (i.e. `x ∈ y + V`). -/
lemma vadd_mem_of_nearest {ℒ : Submodule ℤ E} (y : ℒ) (x : E)
    (h : ∀ z : ℒ, ‖x - (y : E)‖ ≤ ‖x - (z : E)‖) : (-y : E) +ᵥ x ∈ VC ℒ := by
  apply (mem_voronoi_iff_norm (ℒ := ℒ) ((-y : E) + x)).mpr
  intro w
  have hw := h (y + w)
  have hu : ‖x - (y : E)‖ ≤ ‖x - ((y + w : ℒ) : E)‖ := hw
  have hs : ‖x - (y : E)‖ ^ 2 ≤ ‖x - ((y + w : ℒ) : E)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  -- rewrite both sides to the form with u := (-y) + x
  have h1 : x - ((y + w : ℒ) : E) = ((-y : E) + x) - (w : E) := by
    simp only [Submodule.coe_add]
    abel
  have h2 : x - (y : E) = (-y : E) + x := by abel
  rw [h2, h1] at hs
  exact hs

/-- Every point has a closest lattice point. -/
lemma exists_nearest_lattice_point {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (_hℒ : IsZLattice ℝ ℒ) (x : E) : ∃ y : ℒ, ∀ z : ℒ, ‖x - (z : E)‖ ≥ ‖x - (y : E)‖ := by
  classical
  have hclosed : IsClosed (ℒ.toAddSubgroup : Set E) :=
    AddSubgroup.isClosed_of_discrete (G := E) (H := ℒ.toAddSubgroup)
  have hdisc : IsDiscrete (ℒ.toAddSubgroup : Set E) := DiscreteTopology.isDiscrete
  let S : Set ℒ := {z : ℒ | ‖x - (z : E)‖ ≤ ‖x‖}
  have h0 : (0 : ℒ) ∈ S := by
    simp [S]
  have hSfin : S.Finite := by
    have hinj : Set.InjOn (fun z : ℒ => (z : E)) S := (Subtype.coe_injective).injOn
    have himg : (fun z : ℒ => (z : E)) '' S ⊆
        Metric.closedBall x ‖x‖ ∩ (ℒ.toAddSubgroup : Set E) := by
      rintro v ⟨z, hz, rfl⟩
      refine ⟨?_, (Submodule.mem_toAddSubgroup (p := ℒ)).mpr z.2⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      simpa [S, norm_sub_rev] using hz
    have hfin : ((fun z : ℒ => (z : E)) '' S).Finite :=
      (Metric.finite_isBounded_inter_isClosed hdisc Metric.isBounded_closedBall hclosed).subset himg
    exact hfin.of_finite_image hinj
  let F : Finset ℒ := hSfin.toFinset
  have hFmem : ∀ z : ℒ, z ∈ F ↔ z ∈ S := fun z => hSfin.mem_toFinset
  have hFne : F.Nonempty := ⟨(0 : ℒ), (hFmem 0).mpr h0⟩
  obtain ⟨y, hyF, hmin⟩ := Finset.exists_min_image F (fun z : ℒ => ‖x - (z : E)‖) hFne
  refine ⟨y, ?_⟩
  intro z
  by_cases hzS : z ∈ S
  · exact hmin z ((hFmem z).mpr hzS)
  · have hy_le : ‖x - (y : E)‖ ≤ ‖x‖ := (hFmem y).mp hyF
    have hz_gt : ‖x‖ < ‖x - (z : E)‖ := by
      simpa [S] using (lt_of_not_ge hzS)
    exact le_trans hy_le (le_of_lt hz_gt)

/-- Every point lies in some translate of the Voronoi cell. -/
lemma exists_vadd_mem_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (x : E) : ∃ y : ℒ, (y : E) +ᵥ x ∈ VC ℒ := by
  obtain ⟨y₀, hy₀⟩ := exists_nearest_lattice_point (ℒ := ℒ) hℒ x
  refine ⟨-y₀, vadd_mem_of_nearest (ℒ := ℒ) y₀ x hy₀⟩

/-- The overlap of two distinct translates of `V` lies on a hyperplane. -/
lemma inter_vadd_voronoi_subset {ℒ : Submodule ℤ E} (y z : ℒ) (_h : y ≠ z) (x : E)
    (hx : x ∈ (((y : E) +ᵥ VC ℒ) ∩ ((z : E) +ᵥ VC ℒ))) :
    ⟪x - (y : E), ((z - y : ℒ) : E)⟫_ℝ = ‖((z - y : ℒ) : E)‖ ^ 2 / 2 := by
  have hxy : x - (y : E) ∈ VC ℒ := (mem_cell_iff (ℒ := ℒ) y x).mp hx.1
  have hxz : x - (z : E) ∈ VC ℒ := (mem_cell_iff (ℒ := ℒ) z x).mp hx.2
  let u : E := x - (y : E)
  let w : ℒ := z - y
  have huV : u ∈ VC ℒ := hxy
  have huVw : u - (w : E) ∈ VC ℒ := by
    have hEq : u - (w : E) = x - (z : E) := by
      dsimp [u, w]
      abel
    rwa [hEq]
  have h1 := (mem_voronoi_iff_norm (ℒ := ℒ) u).mp huV w
  have h2 := (mem_voronoi_iff_norm (ℒ := ℒ) (u - (w : E))).mp huVw (-w)
  have hsim : (u - (w : E)) - (-(w : E)) = u := by
    abel
  have h2' : ‖u - (w : E)‖ ^ 2 ≤ ‖u‖ ^ 2 := by
    simpa [hsim] using h2
  have hsqeq : ‖u‖ ^ 2 = ‖u - (w : E)‖ ^ 2 := le_antisymm h1 h2'
  have hnorm : ‖u - (w : E)‖ ^ 2 = ‖u‖ ^ 2 + ‖(w : E)‖ ^ 2 - 2 * ⟪u, (w : E)⟫_ℝ := by
    rw [norm_sub_sq_real]
    ring
  have hmain : 2 * ⟪u, (w : E)⟫_ℝ = ‖(w : E)‖ ^ 2 := by
    nlinarith
  -- unfold the lets in the goal
  change ⟪x - (y : E), ((z - y : ℒ) : E)⟫_ℝ = ‖((z - y : ℒ) : E)‖ ^ 2 / 2
  nlinarith [hmain]

/-- The action of a lattice point on the ambient space is addition of its image. -/
@[simp] lemma lattice_vadd_apply {ℒ : Submodule ℤ E} (g : ℒ) (x : E) :
    g +ᵥ x = (g : E) + x := rfl

/-- The cells defined through the lattice action agree with the translates by the images. -/
@[simp] lemma lattice_vadd_cell {ℒ : Submodule ℤ E} (g : ℒ) (s : Set E) :
    g +ᵥ s = ((g : E) +ᵥ s) := by
  ext x
  simp [Set.mem_vadd_set]

/-- A (translated) affine hyperplane has measure zero.  Here the hyperplane is
`{x | ⟪x - p, h⟫ = ‖h‖²/2}` for a nonzero vector `h`. -/
lemma hyperplane_measure_zero (p : E) (h : E) (hh : h ≠ 0) :
    volume {x : E | ⟪x - p, h⟫_ℝ = ‖h‖ ^ 2 / 2} = 0 := by
  let F : E →ₗ[ℝ] ℝ :=
    { toFun := fun x : E => ⟪x, h⟫_ℝ
      map_add' := by intro x y; simp [inner_add_left]
      map_smul' := by intro r x; simp [real_inner_smul_left] }
  let D : Submodule ℝ E := F.ker
  let q : E := p + (1 / 2 : ℝ) • h
  let H : AffineSubspace ℝ E := AffineSubspace.mk' q D
  have hq : ⟪q - p, h⟫_ℝ = ‖h‖ ^ 2 / 2 := by
    dsimp [q]
    congr 1
    abel
    simp [real_inner_smul_left]
    have hs : ‖h‖ ^ 2 = ⟪h, h⟫_ℝ := by
      rw [real_inner_self_eq_norm_sq]
    linarith
  have hsubC : {x : E | ⟪x - p, h⟫_ℝ = ‖h‖ ^ 2 / 2} ⊆ (H : Set E) := by
    intro x hx
    simp [H, D, F]
    have hx' : ⟪x - p, h⟫_ℝ = ‖h‖ ^ 2 / 2 := hx
    have hEq : x - q = (x - p) - (q - p) := by abel
    rw [hEq]
    rw [inner_sub_left]
    linarith
  have hne : (H : Set E).Nonempty := by
    refine ⟨q, ?_⟩
    simp [H, D]
  have hDnt : D ≠ ⊤ := by
    intro htop
    dsimp [D] at htop
    have hF0 : F h = 0 := by
      exact (LinearMap.mem_ker (f := F) (y := h)).mp (by
        rw [htop]
        simp)
    have hhh : ⟪h, h⟫_ℝ = 0 := by simpa [F] using hF0
    have hsq : ‖h‖ ^ 2 = 0 := by
      have hs : ‖h‖ ^ 2 = ⟪h, h⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
      linarith
    exact hh (by
      have hz : ‖h‖ = 0 := sq_eq_zero_iff.mp hsq
      exact norm_eq_zero.mp hz)
  have hHnt : H ≠ ⊤ := by
    have hdir : H.direction = D := AffineSubspace.direction_mk' q D
    intro htop
    exact hDnt (by
      simpa [hdir] using (AffineSubspace.direction_eq_top_iff_of_nonempty (s := H) hne).mpr htop)
  have hmeas : volume (H : Set E) = 0 := Measure.addHaar_affineSubspace volume H hHnt
  exact measure_mono_null hsubC hmeas

/-- The Voronoi cell is a fundamental domain for the translation action of the lattice. -/
lemma isAddFundamentalDomain_voronoi {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) : IsAddFundamentalDomain ℒ (VC ℒ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Submission.Voronoi.voronoi_measurable ℒ).nullMeasurableSet
  · apply Filter.Eventually.of_forall
    intro x
    exact exists_vadd_mem_voronoi hℒ x
  · intro y z hyz
    unfold AEDisjoint
    have hw0 : (z - y : ℒ) ≠ 0 := (sub_ne_zero (a := z) (b := y)).mpr hyz.symm
    have hsub : ((y : ℒ) +ᵥ VC ℒ) ∩ ((z : ℒ) +ᵥ VC ℒ) ⊆
        {x : E | ⟪x - (y : E), ((z - y : ℒ) : E)⟫_ℝ = ‖((z - y : ℒ) : E)‖ ^ 2 / 2} := by
      intro x hx
      exact inter_vadd_voronoi_subset y z hyz x hx
    have hmeas : volume {x : E | ⟪x - (y : E), ((z - y : ℒ) : E)⟫_ℝ = ‖((z - y : ℒ) : E)‖ ^ 2 / 2} = 0 := by
      apply hyperplane_measure_zero (p := (y : E)) (h := ((z - y : ℒ) : E))
      intro hc
      apply hw0
      exact Subtype.ext (by simpa using hc)
    exact measure_mono_null hsub hmeas


/-- The standard Gaussian `e^{-π‖x‖²}` integrates to 1 over the whole space. -/
lemma gaussian_integral_one :
    (∫ x : E, rexp (-Real.pi * ‖x‖ ^ 2)) = 1 := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := Real.pi) Real.pi_pos
  rw [h]
  have hfin : Module.finrank ℝ E = n := by simp
  rw [hfin]
  rw [div_self Real.pi_ne_zero]
  rw [Real.one_rpow]

/-- The Gaussian of width `s` integrates to `s^n` over the whole space. -/
lemma gaussian_integral_sq (s : ℝ) (hs : 0 < s) :
    (∫ x : E, rexp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)) = s ^ n := by
  -- ∫ f(x) dx = s^n · ∫ e^{-π‖u‖²} du via u = s x
  let g : E → ℝ := fun x => rexp (-Real.pi * ‖x‖ ^ 2)
  have hsc := Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure E)) (f := g)
    (R := s) hs.le
  -- hsc : ∫ x, g (s⁻¹ • x) = s ^ finrank • ∫ x, g x   (as vector smul = mul on ℝ)
  have hfin : Module.finrank ℝ E = n := by simp
  rw [hfin] at hsc
  rw [smul_eq_mul] at hsc
  -- now convert g(s⁻¹ • x) to our integrand
  have hEq : (fun x : E => g ((s : ℝ)⁻¹ • x)) = fun x : E => rexp (-Real.pi * ‖x‖ ^ 2 / s ^ 2) := by
    funext x
    have hnorm : ‖(s : ℝ)⁻¹ • x‖ = ‖x‖ / s := by
      rw [norm_smul, Real.norm_eq_abs]
      have hsabs : |(s : ℝ)⁻¹| = s⁻¹ := abs_of_nonneg (inv_nonneg.mpr hs.le)
      rw [hsabs]
      field_simp [hs.ne']
    simp [g, hnorm]
    field_simp [hs.ne']
  -- and ∫ g = 1
  have hg1 : (∫ x : E, g x) = 1 := by simpa [g] using gaussian_integral_one
  rw [← hEq]
  rw [hsc, hg1]
  simp

/-- Integrability of the Gaussian width-`s` density on the whole space. -/
lemma gaussian_integrable (s : ℝ) (hs : 0 < s) :
    Integrable (fun x : E => rexp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [gaussian_integral_sq s hs]
  exact pow_ne_zero n hs.ne'

/-- The Voronoi cell is measurable. -/
lemma voronoi_measurable {ℒ : Submodule ℤ E} : MeasurableSet (VC ℒ) := by
  exact Submission.Voronoi.voronoi_measurable ℒ

/-- A real `2 ≤ e^u + e^{-u}` (cosh ≥ 1). -/
lemma two_le_exp_add_exp_neg (u : ℝ) : 2 ≤ rexp u + rexp (-u) := by
  let a : ℝ := rexp (u / 2)
  let b : ℝ := rexp (-(u / 2))
  have hab : a * b = 1 := by
    dsimp [a, b]
    rw [← Real.exp_add]
    simp
  have hsq : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)
  have hEu : rexp u = a ^ 2 := by
    dsimp [a]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hEneg : rexp (-u) = b ^ 2 := by
    dsimp [b]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith

/-- Translating the Gaussian: `f(y+t) = f(y)·f(t)·e^{-2π⟨y,t⟩/s²}`. -/
lemma gauss_translate_expand (a t : E) (s : ℝ) (hs : s ≠ 0) :
    rexp (-Real.pi * ‖a + t‖ ^ 2 / s ^ 2) =
      rexp (-Real.pi * ‖a‖ ^ 2 / s ^ 2) *
        (rexp (-Real.pi * ‖t‖ ^ 2 / s ^ 2) *
          rexp (-2 * Real.pi * ⟪a, t⟫_ℝ / s ^ 2)) := by
  have hsq : ‖a + t‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, t⟫_ℝ + ‖t‖ ^ 2 := by
    simpa using (norm_add_sq (𝕜 := ℝ) a t)
  have hexp : -Real.pi * ‖a + t‖ ^ 2 / s ^ 2 =
      -Real.pi * ‖a‖ ^ 2 / s ^ 2 +
        (-Real.pi * ‖t‖ ^ 2 / s ^ 2 + -2 * Real.pi * ⟪a, t⟫_ℝ / s ^ 2) := by
    rw [hsq]
    field_simp [hs]
    ring
  rw [hexp]
  rw [Real.exp_add]
  congr 1
  rw [Real.exp_add]

/-- Change of variable: the cell integral at `y` equals the `V`-integral of the shifted density. -/
lemma setIntegral_vadd_cell {ℒ : Submodule ℤ E} (y : ℒ) (f : E → ℝ) :
    (∫ x in (((y : E) +ᵥ VC ℒ)), f x) = ∫ t in VC ℒ, f ((y : E) + t) := by
  let T : E → E := fun t => (y : E) + t
  have hTmp : MeasurePreserving T volume volume := by
    dsimp [T]
    exact measurePreserving_add_left (μ := (volume : Measure E)) (y : E)
  have hTemb : MeasurableEmbedding T := by
    dsimp [T]
    simpa [vadd_eq_add] using (measurableEmbedding_const_vadd (G := E) (α := E) (c := (y : E)))
  have himage : T '' (VC ℒ) = (((y : E) +ᵥ VC ℒ)) := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [Set.mem_vadd_set]
      exact ⟨t, ht, by simp [T]⟩
    · rw [Set.mem_vadd_set]
      rintro ⟨t, ht, hx⟩
      refine ⟨t, ht, ?_⟩
      exact hx
  calc
    (∫ x in (((y : E) +ᵥ VC ℒ)), f x) = ∫ x in (T '' (VC ℒ)), f x := by rw [himage]
    _ = ∫ t in VC ℒ, f (T t) := (hTmp.setIntegral_image_emb hTemb f (VC ℒ))
    _ = ∫ t in VC ℒ, f ((y : E) + t) := by rfl

/-- Reflection-substitution: for a symmetric set, `∫ f(-t) = ∫ f(t)`. -/
lemma setIntegral_comp_neg_symmetric (S : Set E) (hS : ∀ x, x ∈ S → -x ∈ S) (f : E → ℝ) :
    (∫ t in S, f (-t)) = ∫ t in S, f t := by
  have h := Measure.setIntegral_comp_smul (μ := (volume : Measure E)) (f := f) (s := S)
    (R := (-1 : ℝ)) (by norm_num : (-1 : ℝ) ≠ 0)
  have hpow : |((-1 : ℝ) ^ Module.finrank ℝ E)| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have habs : |(((-1 : ℝ) ^ Module.finrank ℝ E)⁻¹)| = 1 := by
    calc
      |(((-1 : ℝ) ^ Module.finrank ℝ E)⁻¹)| = |((-1 : ℝ) ^ Module.finrank ℝ E)|⁻¹ := abs_inv _
      _ = 1 := by rw [hpow]; norm_num
  have hsmul : ((-1 : ℝ) • S) = S := by
    ext y
    constructor
    · intro hy
      rw [Set.mem_smul_set] at hy
      rcases hy with ⟨x, hx, hyx⟩
      have hxneg : -x = y := by simpa using hyx
      rw [← hxneg]
      exact hS x hx
    · intro hy
      rw [Set.mem_smul_set]
      refine ⟨-y, hS y hy, ?_⟩
      simp
  simpa [hsmul, habs] using h

lemma cell_mass_le {ℒ : Submodule ℤ E} (y : ℒ) (s : ℝ) (hs : 0 < s) :
    rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) *
        (∫ t in VC ℒ, rexp (-Real.pi * ‖t‖ ^ 2 / s ^ 2)) ≤
      ∫ t in VC ℒ, rexp (-Real.pi * ‖(y : E) + t‖ ^ 2 / s ^ 2) := by
  let f : E → ℝ := fun t => rexp (-Real.pi * ‖t‖ ^ 2 / s ^ 2)
  let c : ℝ := rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)
  let w : E → ℝ := fun t => f t * rexp (-2 * Real.pi * ⟪(y : E), t⟫_ℝ / s ^ 2)
  let M : ℝ := ∫ t in VC ℒ, f t
  let J : ℝ := ∫ t in VC ℒ, w t
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hfI : Integrable f := by simpa [f] using gaussian_integrable s hs
  have htrans : Integrable (fun t : E => f ((y : E) + t)) := by
    simpa using (Integrable.comp_add_left hfI (y : E))
  have hw_eq : ∀ t : E, f ((y : E) + t) = c * w t := by
    intro t
    have hx := gauss_translate_expand (a := (y : E)) (t := t) s hs.ne'
    dsimp [f, c, w] at hx ⊢
    exact hx
  have hw_alt : w = fun t : E => (c⁻¹ : ℝ) * f ((y : E) + t) := by
    funext t
    have h := congrArg (fun z : ℝ => c⁻¹ * z) (hw_eq t)
    rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul] at h
    exact h.symm
  have hwI : Integrable w := by
    rw [hw_alt]
    simpa using (htrans.const_mul (c⁻¹))
  have hfV : IntegrableOn f (VC ℒ) := (hfI.integrableOn : IntegrableOn f (VC ℒ) volume)
  have hwV : IntegrableOn w (VC ℒ) := (hwI.integrableOn : IntegrableOn w (VC ℒ) volume)
  have hnegI : Integrable (fun t : E => w (-t)) := by
    simpa using hwI.comp_neg
  have hnegV : IntegrableOn (fun t : E => w (-t)) (VC ℒ) :=
    (hnegI.integrableOn : IntegrableOn (fun t : E => w (-t)) (VC ℒ) volume)
  have hsym : (∫ t in VC ℒ, w (-t)) = J := by
    dsimp [J]
    exact setIntegral_comp_neg_symmetric (VC ℒ)
      (fun t ht => Submission.Voronoi.voronoi_neg_mem ht) w
  have hwn : ∀ t : E, w (-t) = f t * rexp (2 * Real.pi * ⟪(y : E), t⟫_ℝ / s ^ 2) := by
    intro t
    dsimp [w, f]
    rw [norm_neg]
    have hin : -2 * Real.pi * ⟪(y : E), -t⟫_ℝ / s ^ 2 = 2 * Real.pi * ⟪(y : E), t⟫_ℝ / s ^ 2 := by
      rw [inner_neg_right]
      ring
    rw [hin]
  have hpt : ∀ t : E, 2 * f t ≤ w t + w (-t) := by
    intro t
    let u : ℝ := 2 * Real.pi * ⟪(y : E), t⟫_ℝ / s ^ 2
    have h2 := two_le_exp_add_exp_neg u
    have hfnon : 0 ≤ f t := by dsimp [f]; positivity
    have hf_even : f (-t) = f t := by
      dsimp [f]
      simp [norm_neg]
    have hwdef : w t = f t * rexp (-u) := by
      dsimp [w, u]
      congr 1
      ring
    have hwneg : w (-t) = f t * rexp u := by
      dsimp [w, u]
      rw [hf_even]
      congr 1
      rw [inner_neg_right]
      ring
    rw [hwdef, hwneg]
    have hlin := mul_le_mul_of_nonneg_left h2 hfnon
    ring_nf at hlin ⊢
    exact hlin
  have hmono : (∫ t in VC ℒ, (2 * f t)) ≤ ∫ t in VC ℒ, (w t + w (-t)) := by
    refine integral_mono_ae ?_ ?_ ?_
    · simpa using (hfV.const_mul (2 : ℝ))
    · exact (hwV.add hnegV)
    · apply Filter.Eventually.of_forall
      intro t
      exact hpt t
  have hsumJ : (∫ t in VC ℒ, (w t + w (-t))) = J + J := by
    have hadd := integral_add (μ := volume.restrict (VC ℒ)) hwV hnegV
    dsimp [J]
    rw [hadd, hsym]
  have h2f : (∫ t in VC ℒ, (2 * f t)) = 2 * M := by
    dsimp [M]
    have hc := integral_const_mul (μ := volume.restrict (VC ℒ)) (r := (2 : ℝ)) f
    simpa [mul_comm] using hc
  have hmain : M ≤ J := by
    have hh : 2 * M ≤ 2 * J := by
      calc
        2 * M = ∫ t in VC ℒ, (2 * f t) := h2f.symm
        _ ≤ ∫ t in VC ℒ, (w t + w (-t)) := hmono
        _ = J + J := hsumJ
        _ = 2 * J := by ring
    exact (le_of_mul_le_mul_left hh (by norm_num : (0 : ℝ) < 2))
  calc
    c * M ≤ c * J := mul_le_mul_of_nonneg_left hmain (le_of_lt hc0)
    _ = ∫ t in VC ℒ, (c * w t) := by
      dsimp [J]
      have hc := integral_const_mul (μ := volume.restrict (VC ℒ)) (r := c) w
      simpa [mul_comm, mul_left_comm, mul_assoc] using hc.symm
    _ = ∫ t in VC ℒ, f ((y : E) + t) := by
      congr 1
      funext t
      exact (hw_eq t).symm
    _ = ∫ t in VC ℒ, rexp (-Real.pi * ‖(y : E) + t‖ ^ 2 / s ^ 2) := by
      dsimp [f]


/-- Cells indexed by a lattice point are measurable. -/
lemma cell_measurableSet {ℒ : Submodule ℤ E} (y : ℒ) :
    MeasurableSet (((y : E) +ᵥ VC ℒ)) := by
  have hmeas : MeasurableSet (VC ℒ) := voronoi_measurable (ℒ := ℒ)
  let T : E → E := fun x => -(y : E) + x
  have hpre : (((y : E) +ᵥ VC ℒ)) = T ⁻¹' (VC ℒ) := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_vadd_set] at hx
      rcases hx with ⟨t, ht, hx⟩
      have hx' : x = (y : E) + t := by simpa using hx.symm
      have hTx : T x = t := by
        dsimp [T]
        rw [hx']
        abel
      rw [Set.mem_preimage]
      rwa [hTx]
    · intro hx
      rw [Set.mem_vadd_set]
      have hTx : T x ∈ VC ℒ := hx
      refine ⟨T x, hTx, ?_⟩
      change (y : E) + (-(y : E) + x) = x
      abel
  rw [hpre]
  exact hmeas.preimage (by
    dsimp [T]
    fun_prop)

/-- For a nonnegative function, the sum over a finite set of lattice points of the masses
of their cells does not exceed the full integral. -/
lemma finiteCellSum_le_integral {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (u : Finset ℒ) (f : E → ℝ) (hf : Integrable f) (hfnon : ∀ x : E, 0 ≤ f x) :
    (∑ y ∈ u, ∫ x in (((y : E) +ᵥ VC ℒ)), f x) ≤ ∫ x : E, f x := by
  classical
  let cells : {y : ℒ // y ∈ u} → Set E := fun y => (((y : ℒ) : E) +ᵥ VC ℒ)
  have hfund : IsAddFundamentalDomain ℒ (VC ℒ) := isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
  have hae : Pairwise fun a b : {y : ℒ // y ∈ u} => AEDisjoint volume (cells a) (cells b) := by
    intro a b hab
    have hab' : (a : ℒ) ≠ (b : ℒ) := by
      intro h
      apply hab
      exact Subtype.ext h
    have h' : AEDisjoint volume (((a : ℒ) +ᵥ VC ℒ)) (((b : ℒ) +ᵥ VC ℒ)) := hfund.aedisjoint hab'
    simpa [cells, lattice_vadd_cell] using h'
  have hnull : ∀ i : {y : ℒ // y ∈ u}, NullMeasurableSet (cells i) volume := by
    intro i
    exact (cell_measurableSet (y := (i : ℒ))).nullMeasurableSet
  have hfU : IntegrableOn f (⋃ i, cells i) :=
    (hf.integrableOn : IntegrableOn f (⋃ i, cells i) volume)
  have hsum := hasSum_integral_iUnion_ae hnull hae hfU
  have hUle : (∫ x in (⋃ i, cells i), f x) ≤ ∫ x : E, f x := by
    have hmeasU : MeasurableSet (⋃ i, cells i) := by
      exact MeasurableSet.iUnion (fun i => cell_measurableSet (y := (i : ℒ)))
    calc
      (∫ x in (⋃ i, cells i), f x) = ∫ x : E, (⋃ i, cells i).indicator f x := by
        rw [MeasureTheory.integral_indicator hmeasU]
      _ ≤ ∫ x : E, f x := by
        refine integral_mono_ae ?_ ?_ ?_
        · exact hf.indicator hmeasU
        · exact hf
        · filter_upwards with x
          by_cases hx : x ∈ ⋃ i, cells i
          · simp [hx]
          · simp [hx, hfnon x]
  have hEqSum : (∑ y ∈ u, ∫ x in (((y : E) +ᵥ VC ℒ)), f x) =
      ∑' i : {y : ℒ // y ∈ u}, ∫ x in cells i, f x := by
    rw [tsum_fintype]
    rw [Finset.univ_eq_attach u]
    simpa [cells] using (Finset.sum_attach u
      (fun y : ℒ => ∫ x in (((y : E) +ᵥ VC ℒ)), f x)).symm
  calc
    (∑ y ∈ u, ∫ x in (((y : E) +ᵥ VC ℒ)), f x)
      = ∑' i : {y : ℒ // y ∈ u}, ∫ x in cells i, f x := hEqSum
    _ = ∫ x in (⋃ i, cells i), f x := hsum.tsum_eq
    _ ≤ ∫ x : E, f x := hUle

/-- ρ_s(ℒ) · γ_s(V(ℒ)) ≤ 1  (Chung–Dadush–Liu–Peikert / paper Lemma 3.4). -/
theorem rho_gamma {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ)
    (s : ℝ) (hs : 0 < s) :
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) *
      (∫ x in {x : E | s • x ∈ VC ℒ}, rexp (-Real.pi * ‖x‖ ^ 2)) ≤ 1 := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  let f : E → ℝ := fun x => rexp (-Real.pi * ‖x‖ ^ 2 / s ^ 2)
  let g : E → ℝ := fun x => rexp (-Real.pi * ‖x‖ ^ 2)
  have hfi : Integrable f := by simpa [f] using gaussian_integrable s hs
  have hmeas : MeasurableSet (VC ℒ) := voronoi_measurable (ℒ := ℒ)
  let M : ℝ := ∫ t in VC ℒ, f t
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    exact setIntegral_nonneg hmeas (fun t ht => by dsimp [f]; positivity)
  have hc_nonneg : ∀ y : ℒ, 0 ≤ rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) := by
    intro y
    positivity
  have htot : (∫ x : E, f x) = ∑' y : ℒ, ∫ t in VC ℒ, f ((y : E) + t) := by
    have hfund : IsAddFundamentalDomain ℒ (VC ℒ) := isAddFundamentalDomain_voronoi (ℒ := ℒ) hℒ
    haveI : VAddInvariantMeasure ℒ E (volume : Measure E) :=
      (inferInstance : VAddInvariantMeasure ℒ.toAddSubgroup E (volume : Measure E))
    have h := MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum'' hfund f hfi
    simpa [lattice_vadd_apply] using h
  have hcell : ∀ y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) * M ≤
      ∫ t in VC ℒ, f ((y : E) + t) := by
    intro y
    simpa [M, f] using cell_mass_le (ℒ := ℒ) y s hs
  have hfinbound : ∀ u : Finset ℒ,
      (∑ y ∈ u, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) * M) ≤ (∫ x : E, f x) := by
    intro u
    calc
      (∑ y ∈ u, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) * M)
          ≤ ∑ y ∈ u, ∫ t in VC ℒ, f ((y : E) + t) := by
            exact Finset.sum_le_sum (fun y hy => hcell y)
      _ = ∑ y ∈ u, ∫ x in (((y : E) +ᵥ VC ℒ)), f x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (setIntegral_vadd_cell (ℒ := ℒ) y f).symm
      _ ≤ ∫ x : E, f x := by
        exact finiteCellSum_le_integral (ℒ := ℒ) hℒ u f hfi (fun x => by dsimp [f]; positivity)
  have htsumc : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) * M) ≤ (∫ x : E, f x) := by
    refine Real.tsum_le_of_sum_le ?_ hfinbound
    intro y
    exact mul_nonneg (hc_nonneg y) hMnonneg
  have hfac : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) * M =
      ∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) * M := by
    have hsm : Summable (fun y : ℒ => rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) := by
      have hc : 0 < Real.pi / s ^ 2 := by positivity
      have h' : Summable (fun y : ℒ => rexp (-(Real.pi / s ^ 2) * ‖(y : E)‖ ^ 2)) :=
        Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq (c := Real.pi / s ^ 2) hc
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h'
    have hsmul := hsm.tsum_const_smul M
    simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using hsmul.symm
  let γ : ℝ := ∫ x in {x : E | s • x ∈ VC ℒ}, rexp (-Real.pi * ‖x‖ ^ 2)
  have hres : ∀ x : E, f x = rexp (-Real.pi * ‖((s : ℝ)⁻¹ • x)‖ ^ 2) := by
    intro x
    dsimp [f]
    congr 1
    rw [norm_smul, Real.norm_eq_abs]
    have hsa : |(s : ℝ)⁻¹| = s⁻¹ := abs_of_nonneg (inv_nonneg.mpr hs.le)
    rw [hsa]
    field_simp [hs.ne']
  have hgamma : γ = (s ^ n)⁻¹ * M := by
    have hpre : {x : E | s • x ∈ VC ℒ} = ((s⁻¹ : ℝ) • (VC ℒ)) := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · intro hx
        refine ⟨s • x, hx, ?_⟩
        rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]
      · rintro ⟨v, hv, hx⟩
        have hmain : s • x = v := by
          rw [← hx]
          rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
        change s • x ∈ VC ℒ
        rw [hmain]
        exact hv
    have hsc := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure E)) (f := g)
      (R := (s : ℝ)⁻¹) (s := VC ℒ) (by positivity : 0 < (s : ℝ)⁻¹)
    have hfinrank : Module.finrank ℝ E = n := by simp
    rw [hfinrank] at hsc
    have hL : (∫ x in VC ℒ, g ((s : ℝ)⁻¹ • x)) = M := by
      have hpw : (fun x : E => g ((s : ℝ)⁻¹ • x)) = f := by
        funext x
        dsimp [g]
        exact (hres x).symm
      rw [hpw]
    have hsc' : M = (s ^ n) * γ := by
      dsimp [γ]
      rw [← hpre] at hsc
      rw [hL] at hsc
      rw [smul_eq_mul] at hsc
      have hinv : (((s : ℝ)⁻¹) ^ n)⁻¹ = s ^ n := by
        rw [inv_pow]
        rw [inv_inv]
      rw [hinv] at hsc
      simpa [g] using hsc
    have hz : s ^ n ≠ 0 := pow_ne_zero n hs.ne'
    calc
      γ = (s ^ n)⁻¹ * (s ^ n * γ) := by field_simp [hz]
      _ = (s ^ n)⁻¹ * M := by rw [hsc']
  calc
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) * γ
        = (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) * ((s ^ n)⁻¹ * M) := by
          rw [hgamma]
    _ = (s ^ n)⁻¹ *
        ((∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) * M) := by ring
    _ = (s ^ n)⁻¹ *
        (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) * M) := by rw [hfac]
    _ ≤ (s ^ n)⁻¹ * (∫ x : E, f x) := by
      exact mul_le_mul_of_nonneg_left htsumc (inv_nonneg.mpr (pow_nonneg hs.le n))
    _ = (s ^ n)⁻¹ * s ^ n := by
      simpa [f] using congrArg (fun z : ℝ => (s ^ n)⁻¹ * z) (gaussian_integral_sq s hs)
    _ = 1 := by
      field_simp [pow_ne_zero n hs.ne']


/-- If the Gaussian mass of the Voronoi cell is at least `2/3`, then `ρ_s(ℒ) ≤ 3/2`. -/
lemma rho_le_three_halves_of_gamma_ge {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (s : ℝ) (hs : 0 < s)
    (hγ : (2 : ℝ) / 3 ≤ ∫ x in {x : E | s • x ∈ VC ℒ}, rexp (-Real.pi * ‖x‖ ^ 2)) :
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) ≤ 3 / 2 := by
  let γ : ℝ := ∫ x in {x : E | s • x ∈ VC ℒ}, rexp (-Real.pi * ‖x‖ ^ 2)
  have hρ : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) * γ ≤ 1 := by
    dsimp [γ]
    exact rho_gamma (ℒ := ℒ) hℒ s hs
  have hγ23 : (2 : ℝ) / 3 ≤ γ := by simpa [γ] using hγ
  have hγpos : 0 < γ := lt_of_lt_of_le (by norm_num) hγ23
  have h1 : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) ≤ γ⁻¹ := by
    have hdiv : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) ≤ (1 : ℝ) / γ :=
      (le_div_iff₀ hγpos).mpr hρ
    simpa using hdiv
  have h2 : γ⁻¹ ≤ 3 / 2 := by
    have hmain : (1 : ℝ) ≤ (3 / 2) * γ := by
      calc
        (1 : ℝ) = (3 / 2) * (2 / 3) := by norm_num
        _ ≤ (3 / 2) * γ := mul_le_mul_of_nonneg_left hγ23 (by norm_num)
    have hprod := mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hγpos.le)
    calc
      γ⁻¹ = 1 * γ⁻¹ := by rw [one_mul]
      _ ≤ ((3 / 2) * γ) * γ⁻¹ := hprod
      _ = (3 / 2) * (γ * γ⁻¹) := by ring
      _ = 3 / 2 := by rw [mul_inv_cancel₀ (ne_of_gt hγpos), mul_one]
  exact le_trans h1 h2

/-- ρ as in `ReverseMinkowski` agrees with the ambient-norm sum over `ℒ`. -/
lemma rho_eq_ambient_sum {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (s : ℝ) : ReverseMinkowski.ρ s ℒ = ∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2) := by
  rfl

end Submission.VoronoiMeasure

import Mathlib
import Submission.Work.Drive.cappedPlane
import Submission.Work.Drive.capDisks_disjoint
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.omegaChainInterface
import Submission.Work.Drive.rotLens_rotCapping_isAction

/-!
# Stage 2: the capped planes are pairwise disjoint

`Work.Drive.exists_strip_cap_disk` supplies the capped plane `P_u = u·M ∪ cap_u` of the configuration
strip of `γ` at the boundary level.  Hugelmeyer's Theorem 2 is applied to a *pairwise disjoint* family
of projective planes, so the present file proves the disjointness:

* `Work.Drive.cappingRel_inl_inl`, `Work.Drive.cappingRel_inr_inr` — two configuration (resp. cap)
  classes of `Work.Drive.CappingSpace` are equal exactly when the underlying pieces are equal;
* `Work.Drive.confOf_injective_of_nonneg` — the capping coordinates `(‖(m, ℓ)‖, (m, ℓ)/‖(m, ℓ)‖, η)`
  determine `(m, η, ℓ)` for `ℓ ≥ 0`;
* `Work.Drive.disjoint_stripImage_rot` — **the configuration strip of `γ` (with its diagonal) is
  disjoint from its rotation by `w` whenever `w ∈ Zc γ`**.  This is the `M ∩ w·M = ∅` half of the
  disjointness; the interior part is the definition of `GoodC`, the boundary part is the injectivity
  of `γ` (together with `0 ∉ Zc γ`);
* `Work.Drive.disjoint_cappedPlane` — the wrapped-up form used by the order theory: the capped plane
  at `u` and the capped plane at `v` are disjoint for `v - u ∈ Zc γ`.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Drive

open scoped Topology

open Submission.Collision (dirC)

open Submission.Geometry (eucNorm eucNorm_pos eucNorm_nonneg)

/-! ## Two classes of `CappingSpace` with the same side are equal iff the points are equal -/

/-- Two configuration classes of `CappingSpace` are equal exactly when the underlying configuration
piece points are equal: `cappingRel` only ever relates a configuration point to a cap point. -/
lemma cappingRel_inl_inl {a b : ConfigPiece} :
    cappingRel (Sum.inl a) (Sum.inl b) ↔ a = b := by
  constructor
  · intro h
    rcases h with h | ⟨r, hr, θ, φ, h | h⟩
    · exact Sum.inl.inj h
    · exact absurd h.2 inl_ne_inr
    · exact absurd h.2 inl_ne_inr
  · intro h; rw [h]; exact Or.inl rfl

/-- Two cap classes of `CappingSpace` are equal exactly when the underlying cap piece points are
equal. -/
lemma cappingRel_inr_inr {a b : CapPiece} :
    cappingRel (Sum.inr a) (Sum.inr b) ↔ a = b := by
  constructor
  · intro h
    rcases h with h | ⟨r, hr, θ, φ, h | h⟩
    · exact Sum.inr.inj h
    · exact absurd h.1 inr_ne_inl
    · exact absurd h.1 inr_ne_inl
  · intro h; rw [h]; exact Or.inl rfl

lemma mk_inl_inj {a b : ConfigPiece} :
    (Quotient.mk'' (Sum.inl a) : CappingSpace) = Quotient.mk'' (Sum.inl b) ↔ a = b := by
  rw [Quotient.eq'']
  exact cappingRel_inl_inl

/-! ## The capping coordinates determine a configuration point -/

/-- **The capping coordinates `(r, z, η)` are injective on configuration points.**  If two triples
`(m, η, ℓ)`, `(m', η', ℓ')` with non-negative length coordinates have the same capping coordinates
`confOf`, they are equal: the radial coordinate and the disk coordinate determine the midpoint, and the
radial coordinate then determines the (non-negative) length. -/
lemma confOf_injective_of_nonneg {p p' : (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hp : 0 ≤ p.2.2) (hp' : 0 ≤ p'.2.2) (h : confOf p = confOf p') : p = p' := by
  rcases p with ⟨m, η, ℓ⟩
  rcases p' with ⟨m', η', ℓ'⟩
  simp only at hp hp'
  simp only [confOf, Prod.mk.injEq] at h
  obtain ⟨hr, hz, heta⟩ := h
  -- `hz` relates the two complex disk coordinates
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only at hre him
  have hD' : 0 ≤ m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2 := by positivity
  have hD : 0 ≤ m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2 := by positivity
  have hs : m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2 = m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2 := by
    have h' := congrArg (fun x => x ^ 2) hr
    rwa [Real.sq_sqrt hD, Real.sq_sqrt hD'] at h'
  have hsqrtne : Real.sqrt (m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2) ≠ 0 ∨
      m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2 = 0 := by
    by_cases h0 : Real.sqrt (m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2) = 0
    · exact Or.inr (le_antisymm (by simpa [Real.sqrt_eq_zero'] using h0) hD')
    · exact Or.inl h0
  have hm1 : m.1 = m'.1 := by
    rcases hsqrtne with h0 | h0
    · have h0' : Real.sqrt (m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2) ≠ 0 := by rwa [hs]
      have h1 : m.1 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2)
          = m'.1 / Real.sqrt (m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2) := hre
      rw [hs] at h1
      exact (div_left_inj' h0).mp h1
    · have h1 : m.1 ^ 2 = 0 := by nlinarith [sq_nonneg m'.1, sq_nonneg m'.2, sq_nonneg ℓ']
      have h2 : m'.1 ^ 2 = 0 := by nlinarith [sq_nonneg m'.1, sq_nonneg m'.2, sq_nonneg ℓ']
      rw [pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)] at h1 h2
      rw [h1, h2]
  have hm2 : m.2 = m'.2 := by
    rcases hsqrtne with h0 | h0
    · have h0' : Real.sqrt (m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2) ≠ 0 := by rwa [hs]
      have h1 : m.2 / Real.sqrt (m.1 ^ 2 + m.2 ^ 2 + ℓ ^ 2)
          = m'.2 / Real.sqrt (m'.1 ^ 2 + m'.2 ^ 2 + ℓ' ^ 2) := him
      rw [hs] at h1
      exact (div_left_inj' h0).mp h1
    · have h1 : m.2 ^ 2 = 0 := by nlinarith [sq_nonneg m'.1, sq_nonneg m'.2, sq_nonneg ℓ']
      have h2 : m'.2 ^ 2 = 0 := by nlinarith [sq_nonneg m'.1, sq_nonneg m'.2, sq_nonneg ℓ']
      rw [pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0)] at h1 h2
      rw [h1, h2]
  have hℓ : ℓ = ℓ' := by
    have hsq : ℓ ^ 2 = ℓ' ^ 2 := by rw [hm1, hm2] at hs; linarith
    nlinarith [hsq, hp, hp']
  have hm : m = m' := Prod.ext hm1 hm2
  rw [hm, heta, hℓ]

/-! ## The configuration strip is disjoint from its rotation by `w ∈ Zc γ` -/

/-- `0 ∉ Zc γ`: the identity rotation is not a "free" angle, i.e. the trivial rotation is a
collision angle (`Work.Drive.zero_mem_GoodC`). -/
lemma zero_notMem_Zc (γ : Circle → ℝ × ℝ) : (0 : UnitAddCircle) ∉ Zc γ :=
  fun h => h (zero_mem_GoodC γ)

open Manifold in
open scoped Manifold ContDiff in
/-- **The configuration strip of `γ` is disjoint from its rotation by `w`, for `w ∈ Zc γ`.**

The strip (`Work.Drive.stripImage`) is the image in the capping space of the configuration map
`μ` (midpoint, doubled direction, length) of `γ`, including its diagonal.  Its rotation by `w`
(`Work.Drive.rotCapping`) adds `w` to the doubled-direction coordinate.

* two *interior* points (positive length) together with the rotation give the configuration collision
  that `w ∈ Zc γ = (GoodC γ)ᶜ` forbids;
* an interior point cannot be the rotation of a boundary (diagonal) point, because the lengths differ;
* two boundary (diagonal) points coincide only if `γ x = γ x'` — hence `x = x'` by injectivity of `γ`
  — and then the directions differ by `w`, forcing `w = 0`, which is excluded by `zero_notMem_Zc`.

This is the `M ∩ w·M = ∅` half of the disjointness of the capped planes. -/
theorem disjoint_stripImage_rot {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {w : UnitAddCircle} (hw : w ∈ Zc γ) :
    Disjoint (stripImage μ) (rotCapping w '' stripImage μ) := by
  have hinj : Function.Injective γ := hγ.isEmbedding.injective
  have hlen_nonneg : ∀ q : Circle × Circle, 0 ≤ (μ q).2.2 := by
    rintro ⟨x, y⟩
    by_cases hxy : x = y
    · subst hxy
      rw [hμdiag x]
    · rw [hμne x y hxy]
      exact eucNorm_nonneg _
  rw [Set.disjoint_left]
  rintro p ⟨q, h1, h2, hp⟩ ⟨y, hy, hyeq⟩
  rw [hp] at hyeq
  obtain ⟨q', h1', h2', hy'⟩ := mem_stripImage_iff.mp hy
  rw [hy'] at hyeq
  rw [rotCapping_mk, rotSum_inl] at hyeq
  have hconfPiece : rotConfig w (confPiece (μ q') h1' h2') = confPiece (μ q) h1 h2 :=
    mk_inl_inj.mp hyeq
  have hval : confOf (μ q) = confOf (Submission.Configuration.actC w (μ q')) := by
    have hv : ((confOf (μ q')).1, (confOf (μ q')).2.1, (confOf (μ q')).2.2 + w)
        = confOf (μ q) := by
      have := congrArg (Subtype.val) hconfPiece
      simpa [confPiece_val, rotConfig] using this
    rw [← hv]
    rfl
  have hμeq : μ q = Submission.Configuration.actC w (μ q') :=
    confOf_injective_of_nonneg (hlen_nonneg q)
      (by rw [Submission.Configuration.actC]; exact hlen_nonneg q') hval
  have hlen_eq : (μ q).2.2 = (Submission.Configuration.actC w (μ q')).2.2 :=
    congrArg (fun z : (ℝ × ℝ) × UnitAddCircle × ℝ => z.2.2) hμeq
  obtain ⟨x, y⟩ := q
  obtain ⟨x', y'⟩ := q'
  by_cases hxy : x = y
  · subst hxy
    by_cases hx'y' : x' = y'
    · -- both configurations are diagonal: injectivity plus `0 ∉ Zc γ`
      subst hx'y'
      have hd := hμeq
      rw [hμdiag x, hμdiag x', Submission.Configuration.actC] at hd
      simp only [Prod.mk.injEq] at hd
      obtain ⟨hγeq, hdir, -⟩ := hd
      have hxx : x = x' := hinj hγeq
      subst hxx
      have hw0 : w = 0 := by
        have h : tangentDirC γ x = tangentDirC γ x + w := hdir
        exact add_left_cancel (a := tangentDirC γ x) (by rw [add_zero]; exact h.symm)
      exact zero_notMem_Zc γ (hw0 ▸ hw)
    · -- `q` diagonal, `q'` interior: the lengths differ
      have hl : (0 : ℝ) = eucNorm (γ x' - γ y') := by
        have h := hlen_eq
        rw [hμdiag x, hμne x' y' hx'y'] at h
        simpa [Submission.Configuration.actC, Submission.Configuration.muOrd] using h
      have hpos : 0 < eucNorm (γ x' - γ y') := by
        refine eucNorm_pos ?_
        intro hzero
        exact hx'y' (hinj (sub_eq_zero.mp hzero))
      linarith [hl, hpos]
  · by_cases hx'y' : x' = y'
    · -- `q` interior, `q'` diagonal: the lengths differ
      subst hx'y'
      have hl : eucNorm (γ x - γ y) = 0 := by
        have h := hlen_eq
        rw [hμne x y hxy, hμdiag x'] at h
        simpa [Submission.Configuration.actC, Submission.Configuration.muOrd] using h
      have hpos : 0 < eucNorm (γ x - γ y) := by
        refine eucNorm_pos ?_
        intro hzero
        exact hxy (hinj (sub_eq_zero.mp hzero))
      linarith [hl, hpos]
    · -- two interior configurations: this is a configuration collision
      rw [hμne x y hxy, hμne x' y' hx'y'] at hμeq
      exact hw ⟨x, y, x', y', hxy, hx'y', hμeq⟩

/-- The composition law of the rotation of the capping space, in application form. -/
lemma rotCapping_apply_add (a b : UnitAddCircle) (x : CappingSpace) :
    rotCapping a (rotCapping b x) = rotCapping (a + b) x := by
  rw [show rotCapping (a + b) = rotCapping a ∘ rotCapping b from rotCapping_add a b,
    Function.comp_apply]

/-- The rotation of the capping space is injective (its inverse is the opposite rotation). -/
lemma rotCapping_injective (a : UnitAddCircle) : Function.Injective (rotCapping a) := by
  intro x y h
  have h1 : rotCapping (-a) (rotCapping a x) = rotCapping (-a) (rotCapping a y) := by rw [h]
  simpa [rotCapping_apply_add, neg_add_cancel, rotCapping_zero] using h1

open Manifold in
open scoped Manifold ContDiff in
/-- **The rotated configuration strips are pairwise disjoint.**  For `v - u ∈ Zc γ` the images of the
configuration strip of `γ` under the rotations by `u` and by `v` are disjoint.  This is the family
version of `Work.Drive.disjoint_stripImage_rot`: the pair `(u, v)` is rotated back to `(0, v - u)` by
the bijection `rotCapping (-u)`, under which the statement is the single one. -/
theorem disjoint_stripImage_rot_family {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ}
    (hμne : ∀ x y : Circle, x ≠ y → μ (x, y) = Submission.Configuration.muOrd γ (x, y))
    (hμdiag : ∀ x : Circle, μ (x, x) = (γ x, tangentDirC γ x, 0))
    {u v : UnitAddCircle} (h : v - u ∈ Zc γ) :
    Disjoint (rotCapping u '' stripImage μ) (rotCapping v '' stripImage μ) := by
  have hbase := disjoint_stripImage_rot hγ hμne hμdiag h
  rw [Set.disjoint_left] at hbase ⊢
  intro x hx hx'
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨y, hy, hyx⟩ := hx'
  have hs_eq : s = rotCapping (v - u) y := by
    apply rotCapping_injective u
    rw [rotCapping_apply_add, ← hyx]
    congr 1
    abel
  exact hbase hs ⟨y, hy, hs_eq.symm⟩


/-! ## The capped plane and its pairwise disjointness -/

/-- **The cap cone of the capping.**  The disk in the cap solid torus `(0,∞) × S¹ × D²` with apex
`(r₀, Θ 0, 0)` and boundary curve `t ↦ (ρ t, Θ t, circleOf (Ψ t))`, shifted by `u` in the `S¹`
coordinate: the points

`((1 - s)·r₀ + s·ρ t,  Θ 0 + s·(Θ t - Θ 0) + u,  s·circleOf (Ψ t))`,  `s ∈ [0,1]`.

Here `Ψ` is the position angle of the curve (`polarLift (ρ t, Ψ t) = γ (exp t)`) and `Θ` the *cap*
angle (`Work.Drive.exists_periodic_cap_angle_polar`), which is `2π`-periodic
(`Work.Drive.capDisks_disjoint` — the same parametrisation).  The value is compared as an element of
`ℝ × UnitAddCircle × ℂ`, so points whose parameters fail the side conditions of `CapPiece` are simply
not in the set. -/
def capCone (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ) (u : UnitAddCircle) : Set CapPiece :=
  {q | ∃ s t : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
    (q : ℝ × UnitAddCircle × ℂ) = ((1 - s) * r₀ + s * ρ t,
      (((Θ 0 + s * (Θ t - Θ 0) : ℝ)) : UnitAddCircle) + u, (s : ℂ) * circleOf (Ψ t))}

/-- **The capped configuration strip at rotation `u`.**  The image in the capping space of the
configuration strip of `γ` together with the disk `Work.Drive.capCone` filling its boundary, rotated
by `u` (`Work.Drive.rotCapping`).  These are the copies of `ℝP²` that Hugelmeyer's Theorem 2 orders;
the parameter `r₀` is the radius of the apex of the cap disk. -/
def cappedPlane (r₀ : ℝ) (ρ Ψ Θ : ℝ → ℝ)
    (μ : Circle × Circle → (ℝ × ℝ) × UnitAddCircle × ℝ) (u : UnitAddCircle) : Set CappingSpace :=
  rotCapping u '' (stripImage μ ∪ Quotient.mk'' '' (Sum.inr '' capCone r₀ ρ Ψ Θ 0))

end Work.Drive

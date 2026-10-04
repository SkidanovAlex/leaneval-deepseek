import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Field.UnitBall
import Mathlib.Tactic.NormNum.RealSqrt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The double of a ball is a sphere

We prove that if a compact Hausdorff space `X` is the union of two closed subsets `A`, `B`, each
homeomorphic to the closed unit ball `D^n ⊆ ℝ^n` by maps `eA`, `eB`, whose intersection is exactly
the boundary sphere of each, and such that the two disk coordinates agree on the intersection, then
`X` is homeomorphic to the unit sphere `S^n ⊆ ℝ^{n+1}`.

The homeomorphism is the obvious one: the upper hemisphere `u ↦ (u, √(1-‖u‖²))` of `D^n` inside
`S^n` is homeomorphic to `D^n` via `D^n ≅ S^n ∩ {last ≥ 0}`, and similarly for the lower
hemisphere `u ↦ (u, -√(1-‖u‖²))`; the two hemispheres meet exactly in the equator, which
corresponds to the boundary spheres of the two disks.
-/

namespace Commons.Topology.Sphere

namespace TwoDiskCover

open Set Metric

variable {n : ℕ}

/-! ### The model: hemispheres of `S^n` -/

/-- The point of `EuclideanSpace ℝ (Fin (n+1))` obtained by appending the real number `s` as last
coordinate to the vector `v`. -/
noncomputable def hemi (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => v i) s)

@[simp] lemma hemi_castSucc (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) (i : Fin n) :
    hemi v s i.castSucc = v i := by simp [hemi]

@[simp] lemma hemi_last (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    hemi v s (Fin.last n) = s := by simp [hemi]

lemma norm_sq_hemi (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    ‖hemi v s‖^2 = ‖v‖^2 + s^2 := by
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc]
  simp [sq]

lemma continuous_hemi : Continuous fun p : EuclideanSpace ℝ (Fin n) × ℝ => hemi p.1 p.2 := by
  have h : Continuous fun p : EuclideanSpace ℝ (Fin n) × ℝ =>
      (Fin.snoc (fun i => p.1 i) p.2 : Fin (n+1) → ℝ) := by
    rw [continuous_pi_iff]
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using continuous_snd
    · intro j
      simp only [Fin.snoc_castSucc]
      fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin (n+1) => ℝ)).comp h

/-- The height `√(1 - ‖v‖²)` of the point of the upper hemisphere of `S^n` above `v`. -/
noncomputable def hgt (v : EuclideanSpace ℝ (Fin n)) : ℝ := Real.sqrt (1 - ‖v‖^2)

/-- The upper hemisphere embedding `u ↦ (u, √(1-‖u‖²))`. -/
noncomputable def upper (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) :=
  hemi v (hgt v)

/-- The lower hemisphere embedding `u ↦ (u, -√(1-‖u‖²))`. -/
noncomputable def lower (v : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) :=
  hemi v (-(hgt v))

lemma continuous_hgt : Continuous (hgt : EuclideanSpace ℝ (Fin n) → ℝ) := by
  unfold hgt; fun_prop

lemma continuous_upper :
    Continuous (upper : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1))) :=
  continuous_hemi.comp (continuous_id.prodMk continuous_hgt)

lemma continuous_lower :
    Continuous (lower : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n+1))) :=
  continuous_hemi.comp (continuous_id.prodMk continuous_hgt.neg)

lemma sq_hgt {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 1) : (hgt v)^2 = 1 - ‖v‖^2 := by
  rw [hgt, Real.sq_sqrt]; nlinarith [norm_nonneg v]

@[simp] lemma hgt_nonneg (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ hgt v := Real.sqrt_nonneg _

@[simp] lemma upper_last (v : EuclideanSpace ℝ (Fin n)) : upper v (Fin.last n) = hgt v := by
  simp [upper]

@[simp] lemma lower_last (v : EuclideanSpace ℝ (Fin n)) : lower v (Fin.last n) = -(hgt v) := by
  simp [lower]

lemma hemi_mem_sphere_iff (v : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    hemi v s ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 ↔ ‖v‖^2 + s^2 = 1 := by
  rw [mem_sphere_zero_iff_norm]
  constructor
  · intro h
    have := norm_sq_hemi v s
    rw [h] at this
    simpa using this.symm
  · intro h
    have h2 : ‖hemi v s‖ ^ 2 = 1 := by rw [norm_sq_hemi, h]
    nlinarith [norm_nonneg (hemi v s)]

lemma upper_mem_sphere {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 1) :
    upper v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := by
  rw [upper, hemi_mem_sphere_iff, sq_hgt hv]; ring

lemma lower_mem_sphere {v : EuclideanSpace ℝ (Fin n)} (hv : ‖v‖ ≤ 1) :
    lower v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 := by
  rw [lower, hemi_mem_sphere_iff, neg_sq, sq_hgt hv]; ring

lemma hemi_inj {v v' : EuclideanSpace ℝ (Fin n)} {s s' : ℝ} (h : hemi v s = hemi v' s') :
    v = v' ∧ s = s' := by
  have h' : ∀ i : Fin (n+1), hemi v s i = hemi v' s' i :=
    fun i => congrFun (congrArg WithLp.ofLp h) i
  refine ⟨?_, by simpa using h' (Fin.last n)⟩
  ext j
  simpa using h' j.castSucc

/-- The upper hemisphere embedding as a map of the closed unit ball into the unit sphere. -/
noncomputable def upperS (u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  ⟨upper u.1, upper_mem_sphere (mem_closedBall_zero_iff.mp u.2)⟩

/-- The lower hemisphere embedding as a map of the closed unit ball into the unit sphere. -/
noncomputable def lowerS (u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1 :=
  ⟨lower u.1, lower_mem_sphere (mem_closedBall_zero_iff.mp u.2)⟩

@[simp] lemma upperS_coe (u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (upperS u : EuclideanSpace ℝ (Fin (n+1))) = upper u.1 := rfl

@[simp] lemma lowerS_coe (u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (lowerS u : EuclideanSpace ℝ (Fin (n+1))) = lower u.1 := rfl

lemma continuous_upperS : Continuous (upperS (n := n)) :=
  Continuous.subtype_mk
    (f := fun u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 => upper u.1)
    (continuous_upper.comp continuous_subtype_val)
    (fun u => upper_mem_sphere (mem_closedBall_zero_iff.mp u.2))

lemma continuous_lowerS : Continuous (lowerS (n := n)) :=
  Continuous.subtype_mk
    (f := fun u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 => lower u.1)
    (continuous_lower.comp continuous_subtype_val)
    (fun u => lower_mem_sphere (mem_closedBall_zero_iff.mp u.2))

lemma upperS_injective : Function.Injective (upperS (n := n)) := by
  intro u v h
  have h' : upper u.1 = upper v.1 := congrArg Subtype.val h
  exact Subtype.ext (hemi_inj h').1

lemma lowerS_injective : Function.Injective (lowerS (n := n)) := by
  intro u v h
  have h' : lower u.1 = lower v.1 := congrArg Subtype.val h
  exact Subtype.ext (hemi_inj h').1

/-- The two hemispheres of `S^n` meet exactly in the equator, which is the image of the boundary
sphere of the disk under both embeddings. -/
lemma upperS_eq_lowerS_iff (a b : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    upperS a = lowerS b ↔
      a.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∧ a = b := by
  constructor
  · intro h
    have h' : upper a.1 = lower b.1 := congrArg Subtype.val h
    have h'' : hemi a.1 (hgt a.1) = hemi b.1 (-(hgt b.1)) := h'
    obtain ⟨h1, h2⟩ := hemi_inj h''
    have ha0 : hgt a.1 = 0 := by linarith [hgt_nonneg a.1, hgt_nonneg b.1]
    have hle : 1 - ‖a.1‖^2 ≤ 0 := Real.sqrt_eq_zero'.mp ha0
    have hge : 0 ≤ 1 - ‖a.1‖^2 := by
      have := mem_closedBall_zero_iff.mp a.2
      nlinarith [norm_nonneg a.1]
    have hsq : ‖a.1‖^2 = 1 := by linarith
    have hnorm : ‖a.1‖ = 1 := by nlinarith [norm_nonneg a.1]
    exact ⟨mem_sphere_zero_iff_norm.mpr hnorm, Subtype.ext h1⟩
  · rintro ⟨ha, rfl⟩
    have hnorm : ‖a.1‖ = 1 := mem_sphere_zero_iff_norm.mp ha
    have hz : hgt a.1 = 0 := by rw [hgt, hnorm]; norm_num
    apply Subtype.ext
    simp only [upperS_coe, lowerS_coe]
    rw [upper, lower, hz, neg_zero]

/-- The first `n` coordinates of a point of `ℝ^{n+1}`. -/
noncomputable def initPt (p : EuclideanSpace ℝ (Fin (n+1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (Fin.init (fun i => p i))

@[simp] lemma initPt_apply (p : EuclideanSpace ℝ (Fin (n+1))) (i : Fin n) :
    initPt p i = p i.castSucc := by
  simp [initPt, Fin.init]

lemma hemi_initPt (p : EuclideanSpace ℝ (Fin (n+1))) :
    hemi (initPt p) (p (Fin.last n)) = p := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ ?_ i
  · rw [hemi_last]
  · intro j
    rw [hemi_castSucc, initPt_apply]

lemma norm_sq_initPt (p : EuclideanSpace ℝ (Fin (n+1))) :
    ‖initPt p‖^2 = ‖p‖^2 - p (Fin.last n)^2 := by
  have h := Fin.sum_univ_castSucc (fun i : Fin (n+1) => p i ^ 2)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, h]
  simp only [initPt_apply]
  ring

lemma norm_initPt {p : EuclideanSpace ℝ (Fin (n+1))}
    (hp : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) : ‖initPt p‖ ≤ 1 := by
  have hnorm : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hsq : ‖initPt p‖^2 = 1 - p (Fin.last n)^2 := by rw [norm_sq_initPt, hnorm]; ring
  nlinarith [norm_nonneg (initPt p), sq_nonneg (p (Fin.last n))]

lemma initPt_mem_closedBall {p : EuclideanSpace ℝ (Fin (n+1))}
    (hp : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) :
    initPt p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 :=
  mem_closedBall_zero_iff.mpr (norm_initPt hp)

lemma upper_initPt_eq {p : EuclideanSpace ℝ (Fin (n+1))}
    (hp : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) (hpos : 0 ≤ p (Fin.last n)) :
    upper (initPt p) = p := by
  have hnorm : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hsq : ‖initPt p‖^2 = 1 - p (Fin.last n)^2 := by rw [norm_sq_initPt, hnorm]; ring
  have hx : 0 ≤ 1 - ‖initPt p‖^2 := by
    nlinarith [norm_nonneg (initPt p), sq_nonneg (p (Fin.last n))]
  have hsqrt : hgt (initPt p) = p (Fin.last n) := by
    rw [hgt, Real.sqrt_eq_iff_eq_sq hx hpos, hsq]
    ring_nf
  rw [upper, hsqrt, hemi_initPt]

lemma lower_initPt_eq {p : EuclideanSpace ℝ (Fin (n+1))}
    (hp : p ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1) (hneg : p (Fin.last n) ≤ 0) :
    lower (initPt p) = p := by
  have hnorm : ‖p‖ = 1 := mem_sphere_zero_iff_norm.mp hp
  have hsq : ‖initPt p‖^2 = 1 - p (Fin.last n)^2 := by rw [norm_sq_initPt, hnorm]; ring
  have hx : 0 ≤ 1 - ‖initPt p‖^2 := by
    nlinarith [norm_nonneg (initPt p), sq_nonneg (p (Fin.last n))]
  have hsqrt : hgt (initPt p) = -(p (Fin.last n)) := by
    rw [hgt, Real.sqrt_eq_iff_eq_sq hx (by linarith), hsq]
    ring_nf
  rw [lower, hsqrt, neg_neg, hemi_initPt]

lemma upperS_initPt {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1}
    (hpos : 0 ≤ (p : EuclideanSpace ℝ (Fin (n+1))) (Fin.last n)) :
    upperS ⟨initPt p.1, initPt_mem_closedBall p.2⟩ = p := by
  apply Subtype.ext
  simp only [upperS_coe]
  exact upper_initPt_eq p.2 hpos

lemma lowerS_initPt {p : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1}
    (hneg : (p : EuclideanSpace ℝ (Fin (n+1))) (Fin.last n) ≤ 0) :
    lowerS ⟨initPt p.1, initPt_mem_closedBall p.2⟩ = p := by
  apply Subtype.ext
  simp only [lowerS_coe]
  exact lower_initPt_eq p.2 hneg

/-- A point of the closed ball lies in its boundary sphere iff its underlying vector has norm one. -/
lemma closedBall_mem_sphere_iff (a : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :
    a ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1 ↔
      a.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  rw [Metric.mem_sphere, Subtype.dist_eq, dist_eq_norm, mem_sphere_zero_iff_norm]
  simp

end TwoDiskCover

section Glue

open Set Classical

variable {X Y : Type*} {A B : Set X}

/-- The proof that a point of `A ∪ B` which is not in `A` lies in `B`. -/
private theorem otherMem (hAB : A ∪ B = Set.univ) (x : X) (hx : x ∉ A) : x ∈ B := by
  rcases (Set.mem_union x A B).mp (by rw [hAB]; exact Set.mem_univ x) with h | h
  · exact absurd h hx
  · exact h

/-- The function obtained by gluing `f : A → Y` and `g : B → Y` along the closed cover `A ∪ B = X`,
using `f` on `A` and `g` elsewhere (where, by the cover assumption, we are on `B`). -/
private noncomputable def paste (hAB : A ∪ B = Set.univ) (f : A → Y) (g : B → Y) : X → Y :=
  fun x => if hx : x ∈ A then f ⟨x, hx⟩ else g ⟨x, otherMem hAB x hx⟩

private lemma paste_mem {hAB : A ∪ B = Set.univ} {f : A → Y} {g : B → Y} {x : X} (hx : x ∈ A) :
    paste hAB f g x = f ⟨x, hx⟩ := by
  rw [paste]
  exact dif_pos hx

private lemma paste_notMem {hAB : A ∪ B = Set.univ} {f : A → Y} {g : B → Y} {x : X} (hx : x ∉ A) :
    paste hAB f g x = g ⟨x, otherMem hAB x hx⟩ := by
  rw [paste]
  exact dif_neg hx


variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Pasting lemma: a function which is continuous on each of two closed sets covering a space is
continuous. -/
private theorem continuous_paste (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = Set.univ)
    (f : A → Y) (g : B → Y) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ (x : A) (y : B), (x : X) = (y : X) → f x = g y) :
    Continuous (paste hAB f g) := by
  have hleft : ContinuousOn (paste hAB f g) A := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : A.domRestrict (paste hAB f g) = f := by
      funext x
      show paste hAB f g (x : X) = f x
      rw [paste_mem x.2]
    rw [hEq]; exact hf
  have hright : ContinuousOn (paste hAB f g) B := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hEq : B.domRestrict (paste hAB f g) = g := by
      funext y
      show paste hAB f g (y : X) = g y
      by_cases hy : (y : X) ∈ A
      · rw [paste_mem hy]
        exact hfg ⟨y, hy⟩ y rfl
      · rw [paste_notMem hy]
    rw [hEq]; exact hg
  have hcont := hleft.union_of_isClosed hright hA hB
  rwa [hAB, continuousOn_univ] at hcont

end Glue

/-- **The double of a ball is a sphere.**  Let `X` be compact Hausdorff with `X = A ∪ B`, where
`A`, `B` are closed and both homeomorphic to the closed unit ball
`D ^ n := Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1` by `eA`, `eB`; suppose the common part
`A ∩ B` is exactly the boundary sphere of each of them (i.e. the preimage of
`Metric.sphere (0 : D^n) 1` under both `eA` and `eB`), and that the two disk coordinates *agree* on
`A ∩ B` (whenever `x : A` and `y : B` represent the same point of `X`, `eA x = eB y`).  Then `X` is
homeomorphic to the unit sphere `S^n ⊆ EuclideanSpace ℝ (Fin (n+1))`.

The map is explicit: every point of `S^n` has non-negative or non-positive last coordinate, and is
`upper (eA x)` or `lower (eB y)` for the two "hemisphere" embeddings
`upper u = (u, +√(1-‖u‖²))`, `lower u = (u, -√(1-‖u‖²))` of `D^n` into `S^n`, whose images meet
exactly in the equator `{u : ‖u‖ = 1}`; the agreement hypothesis makes the piecewise map well
defined, and it is a continuous bijection from a compact space to a Hausdorff space. -/
theorem two_disk_cover {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = Set.univ)
    (eA : A ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (eB : B ≃ₜ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
    (hAc : A ∩ B = eA ⁻¹' (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) 1))
    (hBc : A ∩ B = eB ⁻¹' (Metric.sphere (0 : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin n)) 1) 1))
    (hagree : ∀ (x : A) (y : B), (x : X) = (y : X) → eA x = eB y) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
  classical
  -- A point in `A ∩ B` is on the boundary sphere of the `A`-disk.
  have hsphere_of_mem_inter : ∀ (x : X) (hx : x ∈ A) (hxB : x ∈ B),
      eA ⟨x, hx⟩ ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1 := by
    intro x hx hxB
    have h : x ∈ A ∩ B := ⟨hx, hxB⟩
    rw [hAc] at h
    obtain ⟨a, ha, hax⟩ := h
    have : (⟨x, hx⟩ : A) = a := Subtype.ext hax.symm
    rwa [this]
  -- Conversely, a point of `A` whose `eA`-coordinate is on the boundary sphere lies in `A ∩ B`.
  have hmem_inter_of_sphere : ∀ (x : X) (hx : x ∈ A),
      eA ⟨x, hx⟩ ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1 →
      x ∈ A ∩ B := by
    intro x hx hsph
    rw [hAc]
    exact ⟨⟨x, hx⟩, hsph, rfl⟩
  -- The two pieces agree on the overlap, in hemisphere coordinates.
  have hagree' : ∀ (x : A) (y : B), (x : X) = (y : X) →
      TwoDiskCover.upperS (eA x) = TwoDiskCover.lowerS (eB y) := by
    intro x y hxy
    have hxB : (x : X) ∈ B := hxy ▸ y.2
    have hsph := hsphere_of_mem_inter x x.2 hxB
    have heq : eA x = eB y := hagree x y hxy
    refine (TwoDiskCover.upperS_eq_lowerS_iff (eA x) (eB y)).mpr ⟨?_, heq⟩
    exact (TwoDiskCover.closedBall_mem_sphere_iff (eA x)).mp hsph
  have hcA : Continuous fun a : A => TwoDiskCover.upperS (eA a) :=
    TwoDiskCover.continuous_upperS.comp eA.continuous
  have hcB : Continuous fun b : B => TwoDiskCover.lowerS (eB b) :=
    TwoDiskCover.continuous_lowerS.comp eB.continuous
  have hcont : Continuous (paste hAB (fun a : A => TwoDiskCover.upperS (eA a))
      (fun b : B => TwoDiskCover.lowerS (eB b))) :=
    continuous_paste hA hB hAB _ _ hcA hcB hagree'
  have hleft : ∀ x : A, paste hAB (fun a : A => TwoDiskCover.upperS (eA a))
      (fun b : B => TwoDiskCover.lowerS (eB b)) x = TwoDiskCover.upperS (eA x) :=
    fun x => paste_mem x.2
  have hright : ∀ y : B, paste hAB (fun a : A => TwoDiskCover.upperS (eA a))
      (fun b : B => TwoDiskCover.lowerS (eB b)) y = TwoDiskCover.lowerS (eB y) := by
    intro y
    by_cases hy : (y : X) ∈ A
    · rw [hleft ⟨y, hy⟩]
      exact hagree' ⟨y, hy⟩ y rfl
    · rw [paste_notMem hy]
  -- The glued map is a continuous bijection.
  have hinj : Function.Injective (paste hAB (fun a : A => TwoDiskCover.upperS (eA a))
      (fun b : B => TwoDiskCover.lowerS (eB b))) := by
    intro x y hxy
    have hxA : x ∈ A ∨ x ∈ B := (Set.mem_union x A B).mp (by rw [hAB]; exact Set.mem_univ x)
    have hyA : y ∈ A ∨ y ∈ B := (Set.mem_union y A B).mp (by rw [hAB]; exact Set.mem_univ y)
    have key : ∀ (x : A) (y : B), TwoDiskCover.upperS (eA x) = TwoDiskCover.lowerS (eB y) →
        (x : X) = (y : X) := by
      intro x y h
      obtain ⟨hsph, heq⟩ := (TwoDiskCover.upperS_eq_lowerS_iff (eA x) (eB y)).mp h
      have hsph' : eA x ∈ Metric.sphere (0 : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) 1 :=
        (TwoDiskCover.closedBall_mem_sphere_iff (eA x)).mpr hsph
      have hx' : (x : X) ∈ B := (hmem_inter_of_sphere x x.2 hsph').2
      have h1 : eA x = eB ⟨x, hx'⟩ := hagree x ⟨x, hx'⟩ rfl
      have h2 : (⟨x, hx'⟩ : B) = y := eB.injective (by rw [← heq, ← h1])
      simpa using congrArg Subtype.val h2
    rcases hxA with hxA | hxB <;> rcases hyA with hyA | hyB
    · have h : TwoDiskCover.upperS (eA ⟨x, hxA⟩) = TwoDiskCover.upperS (eA ⟨y, hyA⟩) := by
        rw [← hleft ⟨x, hxA⟩, ← hleft ⟨y, hyA⟩]; exact hxy
      have h2 := TwoDiskCover.upperS_injective h
      simpa using congrArg Subtype.val (eA.injective h2)
    · have h : TwoDiskCover.upperS (eA ⟨x, hxA⟩) = TwoDiskCover.lowerS (eB ⟨y, hyB⟩) := by
        rw [← hleft ⟨x, hxA⟩, ← hright ⟨y, hyB⟩]; exact hxy
      exact key ⟨x, hxA⟩ ⟨y, hyB⟩ h
    · have h : TwoDiskCover.lowerS (eB ⟨x, hxB⟩) = TwoDiskCover.upperS (eA ⟨y, hyA⟩) := by
        rw [← hright ⟨x, hxB⟩, ← hleft ⟨y, hyA⟩]; exact hxy
      exact (key ⟨y, hyA⟩ ⟨x, hxB⟩ h.symm).symm
    · have h : TwoDiskCover.lowerS (eB ⟨x, hxB⟩) = TwoDiskCover.lowerS (eB ⟨y, hyB⟩) := by
        rw [← hright ⟨x, hxB⟩, ← hright ⟨y, hyB⟩]; exact hxy
      have h2 := TwoDiskCover.lowerS_injective h
      simpa using congrArg Subtype.val (eB.injective h2)
  have hsurj : Function.Surjective (paste hAB (fun a : A => TwoDiskCover.upperS (eA a))
      (fun b : B => TwoDiskCover.lowerS (eB b))) := by
    intro p
    rcases le_total ((p : EuclideanSpace ℝ (Fin (n+1))) (Fin.last n)) 0 with hneg | hpos
    · refine ⟨(eB.symm ⟨TwoDiskCover.initPt p.1, TwoDiskCover.initPt_mem_closedBall p.2⟩ : B), ?_⟩
      rw [hright]
      simp only [Homeomorph.apply_symm_apply]
      exact TwoDiskCover.lowerS_initPt hneg
    · refine ⟨(eA.symm ⟨TwoDiskCover.initPt p.1, TwoDiskCover.initPt_mem_closedBall p.2⟩ : A), ?_⟩
      rw [hleft]
      simp only [Homeomorph.apply_symm_apply]
      exact TwoDiskCover.upperS_initPt hpos
  exact ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ ⟨hinj, hsurj⟩) hcont⟩

end Commons.Topology.Sphere
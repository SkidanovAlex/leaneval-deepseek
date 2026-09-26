import Mathlib
import Submission.Commons.Topology.Jordan.bounded_component_of_lattice_polygon
import Submission.Commons.Topology.Jordan.no_continuous_argument_of_bounded_component

set_option autoImplicit true

/-! # The cutting lemma

In an open `Ω ⊆ ℂ`, every loop that is not null-homotopic contains an essential *embedded*
circle.

The classical proof: approximate the loop by a polygonal loop, then take a polygonal loop of
minimal edge count in the essential class; a minimal one has no double point, hence is injective.
-/

namespace Commons.Topology.Plane

open Set Function
open scoped Topology unitInterval
open Commons.Topology.Jordan

noncomputable section

/-- The straight-line segment from `a` to `b`, as a path. -/
def segPath (a b : ℂ) : Path a b where
  toFun t := (1 - (t : ℝ)) • a + (t : ℝ) • b
  continuous_toFun := by fun_prop
  source' := by simp
  target' := by simp

@[simp] lemma segPath_apply (a b : ℂ) (t : I) :
    segPath a b t = (1 - (t : ℝ)) • a + (t : ℝ) • b := rfl

/-- The "clamped" extension of a vertex function: `A k = w (min k N)`. -/
def vext {N : ℕ} (w : Fin (N+1) → ℂ) (k : ℤ) : ℂ :=
  if h : k.toNat ≤ N then w ⟨k.toNat, by omega⟩ else w (Fin.last N)

lemma vext_of_le {N : ℕ} (w : Fin (N+1) → ℂ) (k : ℕ) (hk : k ≤ N) :
    vext w (k:ℤ) = w ⟨k, by omega⟩ := by
  unfold vext
  rw [dif_pos (by simpa using hk)]
  congr 1

/-- The polygonal function of the vertex list `w`, with breakpoints on the uniform grid `k/N`. -/
def polyFun {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (x : ℝ) : ℂ :=
  floorInterp (vext w) ((N:ℝ) * x)

lemma continuous_polyFun {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) : Continuous (polyFun hN w) :=
  (continuous_floorInterp _).comp (by fun_prop)

lemma polyFun_zero {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) : polyFun hN w 0 = w 0 := by
  have h := floorInterp_intCast (vext w) 0
  simp only [Int.cast_zero] at h
  rw [polyFun, mul_zero, h]
  exact vext_of_le w 0 (Nat.zero_le N)

lemma polyFun_one {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) :
    polyFun hN w 1 = w (Fin.last N) := by
  rw [polyFun, mul_one, show ((N:ℕ):ℝ) = ((N:ℤ):ℝ) by push_cast; ring, floorInterp_intCast]
  exact vext_of_le w N le_rfl

lemma polyFun_div {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (k : ℕ) (hk : k ≤ N) :
    polyFun hN w ((k:ℝ)/N) = w ⟨k, by omega⟩ := by
  rw [polyFun, show (N:ℝ) * ((k:ℝ)/N) = (k:ℝ) by field_simp,
    show (k:ℝ) = ((k:ℤ):ℝ) by push_cast; ring, floorInterp_intCast]
  exact vext_of_le w k hk

/-- **The path is affine on each interval `[k/N, (k+1)/N]`** (unscaled form). -/
lemma polyFun_eq_latSeg {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (k : ℤ) (x : ℝ)
    (hx : (N:ℝ) * x ∈ Icc (k:ℝ) ((k:ℝ)+1)) :
    polyFun hN w x = latSeg (vext w) k ((N:ℝ) * x) := by
  rw [polyFun]
  exact floorInterp_eq_latSeg_of_mem_Icc hx

/-- Linearity on a grid interval, stated for the time (not the scaled time). -/
lemma polyFun_eq_latSeg_time {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (k : ℤ) (x : ℝ)
    (hx : (N:ℝ) * x ∈ Icc (k:ℝ) ((k:ℝ)+1)) :
    polyFun hN w x = latSeg (vext w) k ((N:ℝ) * x) := by
  rw [polyFun]
  exact floorInterp_eq_latSeg_of_mem_Icc hx

/-- The value of `polyFun` lies in `Ω`. -/
lemma polyFun_mem {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) {Ω : Set ℂ}
    (hm : ∀ k, w k ∈ Ω) (hseg : ∀ k : Fin N, segment ℝ (w k.castSucc) (w k.succ) ⊆ Ω)
    (x : I) : polyFun hN w (x:ℝ) ∈ Ω := by
  set j : ℤ := ⌊(N:ℝ) * (x:ℝ)⌋ with hj
  have hmem : polyFun hN w (x:ℝ) ∈ segment ℝ (vext w j) (vext w (j+1)) := by
    rw [polyFun]
    exact floorInterp_mem_segment (vext w) ((N:ℝ) * (x:ℝ))
  have hxN : (N:ℝ) * (x:ℝ) ≤ N := by
    have h1 := x.2.2
    have h2 : (0:ℝ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hx0 : 0 ≤ (N:ℝ) * (x:ℝ) := by have h1 := x.2.1; positivity
  have hj0 : 0 ≤ j := by rw [hj]; exact Int.floor_nonneg.mpr hx0
  have hjN : j ≤ (N:ℤ) := by
    rw [hj]
    calc ⌊(N:ℝ) * (x:ℝ)⌋ ≤ ⌊(N:ℝ)⌋ := Int.floor_mono hxN
      _ = (N:ℤ) := Int.floor_natCast N
  have htoNat : j.toNat ≤ N := by omega
  rcases lt_or_eq_of_le htoNat with hlt | heq
  · have h1 : vext w j = w ⟨j.toNat, by omega⟩ := by
      unfold vext; rw [dif_pos (by omega)]
    have hsucc : (j+1).toNat = j.toNat + 1 := by omega
    have h2 : vext w (j+1) = w ⟨j.toNat + 1, by omega⟩ := by
      unfold vext; rw [dif_pos (by omega)]
      congr 1
      exact Fin.ext hsucc
    rw [h1, h2] at hmem
    exact hseg ⟨j.toNat, hlt⟩ hmem
  · have hj_eq : j = (N:ℤ) := by omega
    have h1 : vext w j = w (Fin.last N) := by
      rw [hj_eq]; exact vext_of_le w N le_rfl
    have h2 : vext w (j+1) = w (Fin.last N) := by
      have hgt : ¬((j+1).toNat ≤ N) := by omega
      unfold vext; rw [dif_neg hgt]
    rw [h1, h2] at hmem
    rw [segment_same, mem_singleton_iff] at hmem
    rw [hmem]
    exact hm _

/-- The straight segment from `a` to `b` inside `Ω`, given that the whole segment lies in `Ω`. -/
def segPathΩ {Ω : Set ℂ} {a b : ℂ} (hseg : segment ℝ a b ⊆ Ω) :
    Path (⟨a, hseg (left_mem_segment ℝ a b)⟩ : ↥Ω) ⟨b, hseg (right_mem_segment ℝ a b)⟩ where
  toFun t := ⟨(1 - (t : ℝ)) • a + (t : ℝ) • b, by
    refine hseg ?_
    rw [segment_eq_image]
    exact ⟨(t : ℝ), ⟨t.2.1, t.2.2⟩, rfl⟩⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  source' := Subtype.ext (by simp)
  target' := Subtype.ext (by simp)

@[simp] lemma segPathΩ_coe {Ω : Set ℂ} {a b : ℂ} (hseg : segment ℝ a b ⊆ Ω) (t : I) :
    ((segPathΩ (Ω := Ω) hseg) t : ℂ) = (1 - (t : ℝ)) • a + (t : ℝ) • b := rfl

/-- The polygonal path in `Ω`. -/
def polyPath {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (hm : ∀ k, w k ∈ Ω)
    (hseg : ∀ k : Fin N, segment ℝ (w k.castSucc) (w k.succ) ⊆ Ω) :
    Path (⟨w 0, hm 0⟩ : ↥Ω) ⟨w (Fin.last N), hm _⟩ where
  toFun x := ⟨polyFun hN w (x:ℝ), polyFun_mem hN w hm hseg x⟩
  continuous_toFun := Continuous.subtype_mk
    ((continuous_polyFun hN w).comp continuous_subtype_val) _
  source' := Subtype.ext (polyFun_zero hN w)
  target' := Subtype.ext (polyFun_one hN w)

@[simp] lemma polyPath_apply {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (hm : ∀ k, w k ∈ Ω)
    (hseg : ∀ k : Fin N, segment ℝ (w k.castSucc) (w k.succ) ⊆ Ω) (x : I) :
    ((polyPath hN w hm hseg) x : ℂ) = polyFun hN w (x:ℝ) := rfl

/-- Inside a single grid interval, `polyPath` is a straight segment. -/
lemma polyPath_subpath_coe {N : ℕ} (hN : 0 < N) (w : Fin (N+1) → ℂ) (hm : ∀ k, w k ∈ Ω)
    (hseg : ∀ k : Fin N, segment ℝ (w k.castSucc) (w k.succ) ⊆ Ω)
    {a b : I} {k : ℤ} (ha : (N:ℝ) * (a:ℝ) ∈ Icc (k:ℝ) ((k:ℝ)+1))
    (hb : (N:ℝ) * (b:ℝ) ∈ Icc (k:ℝ) ((k:ℝ)+1)) (t : I) :
    (((polyPath hN w hm hseg).subpath a b) t : ℂ)
      = (1 - (t:ℝ)) * (((polyPath hN w hm hseg) a : ℂ))
        + (t:ℝ) * (((polyPath hN w hm hseg) b : ℂ)) := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hconv : ((Icc.convexComb a b t : I) : ℝ) = (1 - (t:ℝ)) * (a:ℝ) + (t:ℝ) * (b:ℝ) := by
    simp [Icc.coe_convexComb]
  have hmid : (N:ℝ) * ((Icc.convexComb a b t : I) : ℝ) ∈ Icc (k:ℝ) ((k:ℝ)+1) := by
    rw [hconv]
    constructor
    · nlinarith [ha.1, hb.1, t.2.1, t.2.2, hNpos]
    · nlinarith [ha.2, hb.2, t.2.1, t.2.2, hNpos]
  show polyFun hN w ((Icc.convexComb a b t : I) : ℝ) = _
  rw [polyFun_eq_latSeg hN w k _ hmid, hconv, polyPath_apply, polyPath_apply,
    polyFun_eq_latSeg hN w k _ ha, polyFun_eq_latSeg hN w k _ hb]
  simp only [latSeg, Complex.real_smul]
  push_cast
  ring

/-- The grid time `k/N` of the uniform partition. -/
def gtime (N : ℕ) (k : Fin (N+1)) : I := ⟨(k:ℝ)/N, by
  constructor
  · positivity
  · rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp
    · rw [div_le_one (by exact_mod_cast h)]
      exact_mod_cast (by omega : (k:ℕ) ≤ N)⟩

@[simp] lemma gtime_val (N : ℕ) (k : Fin (N+1)) : ((gtime N k : I) : ℝ) = (k:ℝ)/N := rfl

lemma gtime_zero (N : ℕ) : gtime N 0 = 0 := by
  ext; simp [gtime]

lemma gtime_last {N : ℕ} (hN : 0 < N) : gtime N (Fin.last N) = 1 := by
  ext
  simp only [gtime_val, Fin.val_last]
  exact div_self (by exact_mod_cast hN.ne')

lemma gtime_castSucc_le_succ (N : ℕ) (k : Fin N) :
    gtime N k.castSucc ≤ gtime N k.succ := by
  apply Subtype.coe_le_coe.mp
  simp only [gtime_val, Fin.val_castSucc, Fin.val_succ]
  exact div_le_div_of_nonneg_right (by push_cast; linarith) (by positivity)

lemma gtime_monotone (N : ℕ) : Monotone (gtime N) := by
  intro a b hab
  apply Subtype.coe_le_coe.mp
  simp only [gtime_val]
  gcongr
  exact_mod_cast hab

/-- Every time lies in some grid interval. -/
lemma gtime_cover {N : ℕ} (hN : 0 < N) (s : I) :
    ∃ k : Fin N, gtime N k.castSucc ≤ s ∧ s ≤ gtime N k.succ := by
  set j : ℕ := min ⌊(N:ℝ) * (s:ℝ)⌋₊ (N-1) with hj
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hjN : j < N := by
    rw [hj]
    have : min ⌊(N:ℝ) * (s:ℝ)⌋₊ (N-1) ≤ N-1 := min_le_right _ _
    omega
  have hle : (j:ℝ) ≤ (N:ℝ) * (s:ℝ) := by
    have h1 : (j:ℝ) ≤ (⌊(N:ℝ) * (s:ℝ)⌋₊ : ℝ) := by
      rw [hj]; exact_mod_cast min_le_left _ _
    have h2 : (⌊(N:ℝ) * (s:ℝ)⌋₊ : ℝ) ≤ (N:ℝ) * (s:ℝ) :=
      Nat.floor_le (by nlinarith [s.2.1, Nat.cast_nonneg (α := ℝ) N])
    linarith
  have hge : (N:ℝ) * (s:ℝ) ≤ (j:ℝ) + 1 := by
    by_cases hcase : ⌊(N:ℝ) * (s:ℝ)⌋₊ < N
    · have hj' : j = ⌊(N:ℝ) * (s:ℝ)⌋₊ := by rw [hj]; exact min_eq_left (by omega)
      have h2 : (N:ℝ) * (s:ℝ) < (⌊(N:ℝ) * (s:ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [hj']; linarith
    · have hs1 : (N:ℝ) * (s:ℝ) ≤ N := by
        have h1 := s.2.2; nlinarith [Nat.cast_nonneg (α := ℝ) N]
      have hj' : j = N - 1 := by rw [hj]; exact min_eq_right (by omega)
      rw [hj']
      have hcast : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
        rw [Nat.cast_sub hN]; norm_num
      rw [hcast]; linarith
  refine ⟨⟨j, hjN⟩, ?_, ?_⟩
  · apply Subtype.coe_le_coe.mp
    simp only [gtime_val, Fin.val_castSucc]
    rw [div_le_iff₀ hNpos]
    push_cast
    linarith
  · apply Subtype.coe_le_coe.mp
    simp only [gtime_val, Fin.val_succ]
    rw [le_div_iff₀ hNpos]
    push_cast
    linarith


section Descent

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- The `2π`-periodic unrolling of the loop `p`. -/
private noncomputable def loopPer (p : Path x x) (t : ℝ) : X :=
  p (Set.projIcc 0 1 zero_le_one (t / (2 * Real.pi)))

private lemma continuous_loopPer (p : Path x x) : Continuous (loopPer p) :=
  p.continuous.comp (continuous_projIcc.comp (by fun_prop))

private lemma loopPer_zero (p : Path x x) : loopPer p 0 = x := by
  rw [loopPer, zero_div, Set.projIcc_left]
  exact p.source

private lemma loopPer_two_pi (p : Path x x) : loopPer p (2 * Real.pi) = x := by
  rw [loopPer, div_self (by positivity), Set.projIcc_right]
  exact p.target

private lemma loopPer_apply (p : Path x x) (t : ℝ) :
    loopPer p t = p (Set.projIcc 0 1 zero_le_one (t / (2 * Real.pi))) := rfl

/-- The descent of the loop `p` to a map on the circle. -/
noncomputable def loopCircleMap (p : Path x x) : C(Circle, X) :=
  haveI : Fact (0 < (2:ℝ) * Real.pi) := ⟨by positivity⟩
  ⟨fun z => AddCircle.liftIco (2 * Real.pi) 0 (loopPer p) ((AddCircle.homeomorphCircle').symm z),
    (AddCircle.liftIco_zero_continuous (p := 2 * Real.pi)
      (by rw [loopPer_zero, loopPer_two_pi]) (continuous_loopPer p).continuousOn).comp
      (AddCircle.homeomorphCircle').symm.continuous⟩

private lemma circleMap_exp (p : Path x x) (θ : ℝ) :
    (AddCircle.homeomorphCircle').symm (Circle.exp θ) = ((θ : ℝ) : AddCircle (2 * Real.pi)) := by
  rw [← AddCircle.homeomorphCircle'_apply_mk (x := θ)]
  exact (AddCircle.homeomorphCircle').symm_apply_apply _

/-- On `[0,1]` the descent agrees with the original loop. -/
lemma circleMap_apply (p : Path x x) (s : Set.Icc (0:ℝ) 1) :
    loopCircleMap p (Circle.exp (2 * Real.pi * (s : ℝ))) = p s := by
  haveI : Fact (0 < (2:ℝ) * Real.pi) := ⟨by positivity⟩
  show AddCircle.liftIco (2 * Real.pi) 0 (loopPer p)
      ((AddCircle.homeomorphCircle').symm (Circle.exp (2 * Real.pi * (s : ℝ)))) = p s
  rcases eq_or_lt_of_le s.2.2 with h1 | h1
  · have hs : s = (1 : Set.Icc (0:ℝ) 1) := Subtype.ext (by exact_mod_cast h1)
    rw [hs]
    have hexp : Circle.exp (2 * Real.pi * (((1 : Set.Icc (0:ℝ) 1)) : ℝ)) = Circle.exp 0 := by
      rw [show 2 * Real.pi * (((1 : Set.Icc (0:ℝ) 1)) : ℝ) = 2 * Real.pi by
        rw [Set.Icc.coe_one, mul_one], Circle.exp_two_pi, Circle.exp_zero]
    rw [hexp, circleMap_exp p 0]
    rw [AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := (0:ℝ)) (f := loopPer p)
      (by refine ⟨le_refl 0, ?_⟩; positivity)]
    rw [loopPer_zero]
    exact p.target.symm
  · have hs : (2 * Real.pi * (s:ℝ)) ∈ Set.Ico (0:ℝ) (0 + 2 * Real.pi) := by
      constructor
      · have := s.2.1; positivity
      · have := s.2.2; nlinarith [Real.pi_pos]
    rw [circleMap_exp p (2 * Real.pi * s)]
    rw [AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := (0:ℝ)) (f := loopPer p) hs]
    show p (Set.projIcc (0:ℝ) 1 zero_le_one ((2 * Real.pi * (s:ℝ)) / (2 * Real.pi))) = p s
    rw [show (2 * Real.pi * (s:ℝ)) / (2 * Real.pi) = (s:ℝ) by field_simp,
      show Set.projIcc (0:ℝ) 1 zero_le_one (s:ℝ) = s from
        Set.projIcc_of_mem (h := zero_le_one) (x := (s:ℝ)) s.2]

/-! ## Square bookkeeping (following `Topology.Plane.simplyConnected...`) -/

private def sqBot (G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X)) :
    Path (G (0, 0)) (G (1, 0)) where
  toFun s := G (s, 0)
  continuous_toFun := G.continuous.comp (by fun_prop)
  source' := rfl
  target' := rfl

private def sqRight (G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X)) :
    Path (G (1, 0)) (G (1, 1)) where
  toFun t := G (1, t)
  continuous_toFun := G.continuous.comp (by fun_prop)
  source' := rfl
  target' := rfl

private def sqTop (G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X)) :
    Path (G (0, 1)) (G (1, 1)) where
  toFun s := G (s, 1)
  continuous_toFun := G.continuous.comp (by fun_prop)
  source' := rfl
  target' := rfl

private def sqLeft (G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X)) :
    Path (G (0, 0)) (G (0, 1)) where
  toFun t := G (0, t)
  continuous_toFun := G.continuous.comp (by fun_prop)
  source' := rfl
  target' := rfl

private def botSeg : Path ((0,0) : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) (1, 0) where
  toFun s := (s, 0)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def rightSeg : Path ((1,0) : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) (1, 1) where
  toFun t := (1, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def leftSeg : Path ((0,0) : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) (0, 1) where
  toFun t := (0, t)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

private def topSeg : Path ((0,1) : Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) (1, 1) where
  toFun s := (s, 1)
  continuous_toFun := by fun_prop
  source' := rfl
  target' := rfl

/-- The two boundary routes of a square are homotopic. -/
private lemma square_boundary (G : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X)) :
    ((sqBot G).trans (sqRight G)).Homotopic ((sqLeft G).trans (sqTop G)) := by
  haveI h1 : ContractibleSpace ↥(Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1) :=
    ((convex_Icc (0:ℝ) 1).prod (convex_Icc (0:ℝ) 1)).contractibleSpace ⟨(0, 0), by simp⟩
  haveI h2 : ContractibleSpace (Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) :=
    (Homeomorph.Set.prod (Set.Icc (0:ℝ) 1) (Set.Icc (0:ℝ) 1)).symm.contractibleSpace
  haveI : SimplyConnectedSpace (Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1) :=
    SimplyConnectedSpace.ofContractible _
  have hAB : (botSeg.trans rightSeg).Homotopic (leftSeg.trans topSeg) :=
    SimplyConnectedSpace.paths_homotopic _ _
  have hmap := hAB.map G
  have e1 : ((botSeg.trans rightSeg).map G.continuous) = (sqBot G).trans (sqRight G) := by
    rw [Path.map_trans]; congr 1
  have e2 : ((leftSeg.trans topSeg).map G.continuous) = (sqLeft G).trans (sqTop G) := by
    rw [Path.map_trans]; congr 1
  rwa [e1, e2] at hmap

/-- Casting a concatenation. -/
private lemma cast_trans_eq {Y : Type*} [TopologicalSpace Y] {a b c a' b' c' : Y}
    (γ : Path a b) (δ : Path b c) (h1 : a' = a) (h2 : b' = b) (h3 : c' = c) :
    (γ.cast h1 h2).trans (δ.cast h2 h3) = (γ.trans δ).cast h1 h3 := by
  ext t
  rw [Path.trans_apply]
  rw [show ((γ.trans δ).cast h1 h3) t = (γ.trans δ) t from rfl, Path.trans_apply]
  split_ifs <;> rfl

/-- **A free null-homotopy of the descended circle map gives a based null-homotopy of the
loop.** -/
theorem homotopic_refl_of_nullhomotopic_circleMap (p : Path x x)
    (h : (loopCircleMap p).Nullhomotopic) : p.Homotopic (Path.refl x) := by
  obtain ⟨c, ⟨H⟩⟩ := h
  let F : C(Set.Icc (0:ℝ) 1 × Set.Icc (0:ℝ) 1, X) :=
    ⟨fun q => H (q.2, Circle.exp (2 * Real.pi * (q.1 : ℝ))),
      H.continuous.comp (continuous_snd.prodMk
        (Circle.exp.continuous.comp
          (continuous_const.mul (continuous_subtype_val.comp continuous_fst))))⟩
  have hF0 : ∀ s : Set.Icc (0:ℝ) 1, F (s, 0) = p s := by
    intro s
    change H.toFun ((0 : Set.Icc (0:ℝ) 1), Circle.exp (2 * Real.pi * (s:ℝ))) = p s
    rw [ContinuousMap.Homotopy.map_zero_left, circleMap_apply]
  have hF1 : ∀ s : Set.Icc (0:ℝ) 1, F (s, 1) = c := by
    intro s
    change H.toFun ((1 : Set.Icc (0:ℝ) 1), Circle.exp (2 * Real.pi * (s:ℝ))) = c
    rw [ContinuousMap.Homotopy.map_one_left]
    rfl
  have hFs : ∀ τ : Set.Icc (0:ℝ) 1, F (0, τ) = F (1, τ) := by
    intro τ
    change H.toFun (τ, Circle.exp (2 * Real.pi * (((0 : Set.Icc (0:ℝ) 1)) : ℝ)))
        = H.toFun (τ, Circle.exp (2 * Real.pi * (((1 : Set.Icc (0:ℝ) 1)) : ℝ)))
    rw [show 2 * Real.pi * (((0 : Set.Icc (0:ℝ) 1)) : ℝ) = 0 by
          rw [Set.Icc.coe_zero, mul_zero],
      show 2 * Real.pi * (((1 : Set.Icc (0:ℝ) 1)) : ℝ) = 2 * Real.pi by
          rw [Set.Icc.coe_one, mul_one],
      Circle.exp_zero, Circle.exp_two_pi]
  have ha : F (0,0) = x := (hF0 0).trans p.source
  have hb : F (1,0) = x := (hF0 1).trans p.target
  have he : F (0,1) = c := hF1 0
  have hd : F (1,1) = c := hF1 1
  set P1 : Path x x := (sqBot F).cast ha.symm hb.symm with hP1
  set P2 : Path x c := (sqRight F).cast hb.symm hd.symm with hP2
  set P3 : Path x c := (sqLeft F).cast ha.symm he.symm with hP3
  set P4 : Path c c := (sqTop F).cast he.symm hd.symm with hP4
  have hP1f : ∀ s, P1 s = p s := by
    intro s; rw [hP1, Path.cast_coe]; exact hF0 s
  have hP3f : ∀ t, P3 t = P2 t := by
    intro t; rw [hP3, hP2, Path.cast_coe, Path.cast_coe]; exact hFs t
  have hP4f : ∀ s, P4 s = c := by
    intro s; rw [hP4, Path.cast_coe]; exact hF1 s
  have hP1p : P1.Homotopic p := by rw [Path.ext (funext hP1f)]
  have hP3P2 : P3.Homotopic P2 := by rw [Path.ext (funext hP3f)]
  have hP4r : P4.Homotopic (Path.refl c) := by
    rw [Path.ext (funext fun s => show P4 s = (Path.refl c) s from hP4f s)]
  have hA : (((sqBot F).trans (sqRight F)).cast ha.symm hd.symm).Homotopic
      (((sqLeft F).trans (sqTop F)).cast ha.symm hd.symm) :=
    (square_boundary F).pathCast ha.symm hd.symm
  rw [← cast_trans_eq (sqBot F) (sqRight F) ha.symm hb.symm hd.symm,
    ← cast_trans_eq (sqLeft F) (sqTop F) ha.symm he.symm hd.symm] at hA
  have key : (p.trans P2).Homotopic (P2.trans (Path.refl c)) :=
    (Path.Homotopic.hcomp hP1p.symm (Path.Homotopic.refl P2)).trans
      (hA.trans (Path.Homotopic.hcomp hP3P2 hP4r))
  exact ((Path.Homotopic.trans_refl p).symm).trans
    (((Path.Homotopic.hcomp (Path.Homotopic.refl p) (Path.Homotopic.trans_symm P2).symm).trans
      (((Path.Homotopic.trans_assoc p P2 P2.symm).symm).trans
        ((Path.Homotopic.hcomp key (Path.Homotopic.refl P2.symm)).trans
          ((Path.Homotopic.trans_assoc P2 (Path.refl c) P2.symm).trans
            ((Path.Homotopic.hcomp (Path.Homotopic.refl P2)
              (Path.Homotopic.refl_trans P2.symm)).trans
              (Path.Homotopic.trans_symm P2)))))))

/-- **Injectivity of the descended circle map.** -/
lemma circleMap_injective (p : Path x x)
    (hinj : Set.InjOn p (Set.Ico (0 : Set.Icc (0:ℝ) 1) 1)) :
    Function.Injective (loopCircleMap p) := by
  haveI : Fact (0 < (2:ℝ) * Real.pi) := ⟨by positivity⟩
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hg : Function.Injective (AddCircle.liftIco (2 * Real.pi) 0 (loopPer p)) := by
    intro u v huv
    obtain ⟨a, ha, rfl⟩ := AddCircle.eq_coe_Ico (p := (2 * Real.pi)) u
    obtain ⟨b, hb, rfl⟩ := AddCircle.eq_coe_Ico (p := (2 * Real.pi)) v
    have ha' : a ∈ Set.Ico (0:ℝ) (0 + 2 * Real.pi) := by simpa using ha
    have hb' : b ∈ Set.Ico (0:ℝ) (0 + 2 * Real.pi) := by simpa using hb
    have hua : AddCircle.liftIco (2 * Real.pi) 0 (loopPer p) (↑a)
        = p (Set.projIcc 0 1 zero_le_one (a / (2 * Real.pi))) := by
      rw [AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := (0:ℝ)) (f := loopPer p) ha']
      exact loopPer_apply p a
    have hvb : AddCircle.liftIco (2 * Real.pi) 0 (loopPer p) (↑b)
        = p (Set.projIcc 0 1 zero_le_one (b / (2 * Real.pi))) := by
      rw [AddCircle.liftIco_coe_apply (p := 2 * Real.pi) (a := (0:ℝ)) (f := loopPer p) hb']
      exact loopPer_apply p b
    rw [hua, hvb] at huv
    have hpa : a / (2 * Real.pi) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg ha.1 hpi.le, (div_le_one hpi).mpr ha.2.le⟩
    have hpb : b / (2 * Real.pi) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨div_nonneg hb.1 hpi.le, (div_le_one hpi).mpr hb.2.le⟩
    have hlt_a : a / (2 * Real.pi) < 1 := (div_lt_one hpi).mpr ha.2
    have hlt_b : b / (2 * Real.pi) < 1 := (div_lt_one hpi).mpr hb.2
    rw [Set.projIcc_of_mem (h := zero_le_one) hpa,
      Set.projIcc_of_mem (h := zero_le_one) hpb] at huv
    have hsa : (⟨a / (2 * Real.pi), hpa⟩ : Set.Icc (0:ℝ) 1) ∈ Set.Ico (0 : Set.Icc (0:ℝ) 1) 1 :=
      ⟨by simp, by rw [Subtype.mk_lt_mk]; exact hlt_a⟩
    have hsb : (⟨b / (2 * Real.pi), hpb⟩ : Set.Icc (0:ℝ) 1) ∈ Set.Ico (0 : Set.Icc (0:ℝ) 1) 1 :=
      ⟨by simp, by rw [Subtype.mk_lt_mk]; exact hlt_b⟩
    have habval : a / (2 * Real.pi) = b / (2 * Real.pi) :=
      congrArg Subtype.val (hinj hsa hsb huv)
    have hab' : a = b := by
      have h := congrArg (fun x : ℝ => x * (2 * Real.pi)) habval
      rw [div_mul_cancel₀ _ (ne_of_gt hpi), div_mul_cancel₀ _ (ne_of_gt hpi)] at h
      exact h
    rw [hab']
  intro z w hzw
  exact (AddCircle.homeomorphCircle').symm.injective (hg hzw)

end Descent
structure PolyLoop (Ω : Set ℂ) where
  M : ℕ
  hM : 0 < M
  base : ↥Ω
  loop : Path base base
  t : Fin (M+1) → I
  ht0 : t 0 = 0
  ht1 : t (Fin.last M) = 1
  htmono : Monotone t
  haff : ∀ (k : Fin M) (u : I),
    ((loop (Icc.convexComb (t k.castSucc) (t k.succ) u) : ↥Ω) : ℂ)
      = (1 - (u:ℝ)) * (((loop (t k.castSucc) : ↥Ω) : ℂ))
        + (u:ℝ) * (((loop (t k.succ) : ↥Ω) : ℂ))

namespace PolyLoop

variable {Ω : Set ℂ}

/-- A polygonal loop is *essential* when its loop is not null-homotopic. -/
def Essential (L : PolyLoop Ω) : Prop := ¬ L.loop.Homotopic (Path.refl L.base)

/-- The circle map of a polygonal loop. -/
noncomputable def toCircle (L : PolyLoop Ω) : C(Circle, ↥Ω) := loopCircleMap L.loop

/-- An essential polygonal loop has a circle map which is not null-homotopic. -/
lemma not_nullhomotopic_toCircle (L : PolyLoop Ω) (h : L.Essential) :
    ¬ L.toCircle.Nullhomotopic := fun hc =>
  h (homotopic_refl_of_nullhomotopic_circleMap L.loop hc)

/-- If the loop is injective on the first half-open period, so is its circle map. -/
lemma toCircle_injective (L : PolyLoop Ω)
    (hinj : Set.InjOn L.loop (Set.Ico (0 : Set.Icc (0:ℝ) 1) 1)) :
    Function.Injective L.toCircle :=
  circleMap_injective L.loop hinj

end PolyLoop

namespace PolyLoop

variable {Ω : Set ℂ}

/-- The set of grid indices `k` with `L.t k ≤ s`. -/
def idxSet (L : PolyLoop Ω) (s : I) : Finset (Fin L.M) :=
  Finset.filter (fun k : Fin L.M => L.t k.castSucc ≤ s) Finset.univ

lemma idxSet_nonempty (L : PolyLoop Ω) (s : I) : (L.idxSet s).Nonempty := by
  refine ⟨⟨0, L.hM⟩, ?_⟩
  rw [idxSet, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  have h0 : ((⟨0, L.hM⟩ : Fin L.M).castSucc) = (0 : Fin (L.M+1)) := by ext; simp
  rw [h0, L.ht0]
  exact s.2.1

/-- The grid index of a time: the largest `k` with `L.t k.castSucc ≤ s`. -/
noncomputable def gidx (L : PolyLoop Ω) (s : I) : Fin L.M :=
  (L.idxSet s).max' (L.idxSet_nonempty s)

lemma gidx_le (L : PolyLoop Ω) (s : I) : L.t (L.gidx s).castSucc ≤ s := by
  have := Finset.max'_mem (L.idxSet s) (L.idxSet_nonempty s)
  unfold idxSet at this
  rw [Finset.mem_filter] at this
  exact this.2

lemma le_gidx_succ (L : PolyLoop Ω) (s : I) : s ≤ L.t (L.gidx s).succ := by
  set k := L.gidx s with hk
  have hk' : L.t k.castSucc ≤ s := by rw [hk]; exact gidx_le L s
  by_contra h
  rw [not_le] at h
  have hk1 : (k:ℕ) + 1 < L.M := by
    by_contra hc
    have hkM : (k:ℕ) + 1 = L.M := by omega
    have hspec : L.t (⟨L.M, by omega⟩ : Fin (L.M+1)) = 1 := L.ht1
    have : L.t k.succ = 1 := by
      rw [show k.succ = (⟨L.M, by omega⟩ : Fin (L.M+1)) from by
        apply Fin.ext; simp [Fin.val_succ]; omega, hspec]
    rw [this] at h
    exact absurd s.2.2 (not_le.mpr h)
  have hmem : (⟨(k:ℕ)+1, hk1⟩ : Fin L.M) ∈ L.idxSet s := by
    unfold idxSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hcast : (⟨(k:ℕ)+1, hk1⟩ : Fin L.M).castSucc = k.succ := by
      apply Fin.ext; simp
    rw [hcast]
    exact le_of_lt h
  have h2 : (⟨(k:ℕ)+1, hk1⟩ : Fin L.M) ≤ L.gidx s := by
    unfold gidx
    exact Finset.le_max' _ _ hmem
  rw [← hk] at h2
  have h3 : ((⟨(k:ℕ)+1, hk1⟩ : Fin L.M) : ℕ) ≤ (k:ℕ) := h2
  simp only [Fin.val_mk] at h3
  omega

end PolyLoop


/-- **Approximation.**  Every loop that is not null-homotopic in an open `Ω ⊆ ℂ` is homotopic to
a polygonal loop, which is therefore essential. -/
theorem exists_essential_polyLoop {Ω : Set ℂ} (hΩ : IsOpen Ω) {x : ↥Ω}
    (p : Path x x) (hp : ¬ p.Homotopic (Path.refl x)) :
    ∃ L : PolyLoop Ω, L.Essential := by
  classical
  set γ : I → ℂ := fun t => ((p t : ↥Ω) : ℂ) with hγ
  have hγc : Continuous γ := continuous_subtype_val.comp p.continuous
  -- a positive distance from the image of `γ` to the complement of `Ω`
  have hdist : ∃ δ > 0, ∀ z ∈ Set.range γ, ∀ w : ℂ, dist z w < δ → w ∈ Ω := by
    have hcomp : IsCompact (Set.range γ) := isCompact_range hγc
    have hne : (Set.range γ).Nonempty := ⟨γ 0, 0, rfl⟩
    by_cases hDne : (Ωᶜ).Nonempty
    · obtain ⟨δ, hδpos, hδ'⟩ :=
        Commons.Topology.Jordan.exists_pos_infDist_of_isCompact_of_isClosed
          hcomp hne hΩ.isClosed_compl hDne
          (Set.disjoint_left.mpr fun z hz1 hz2 => by
            obtain ⟨t, rfl⟩ := hz1
            exact hz2 (p t).2)
      refine ⟨δ, hδpos, fun z hz w hw => ?_⟩
      by_contra hwΩ
      have h1 : δ ≤ Metric.infDist z (Ωᶜ) := hδ' z hz
      have h2 : Metric.infDist z (Ωᶜ) ≤ dist z w :=
        Metric.infDist_le_dist_of_mem (by simpa using hwΩ)
      linarith
    · exact ⟨1, one_pos, fun z hz w hw => by
        by_contra hwΩ
        exact hDne ⟨w, hwΩ⟩⟩
  obtain ⟨δ, hδpos, hδΩ⟩ := hdist
  -- uniform continuity gives a mesh
  obtain ⟨η, hηpos, hη⟩ :=
    Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous p.continuous)
      δ hδpos
  obtain ⟨N, hN, hNη⟩ : ∃ N : ℕ, 0 < N ∧ 1/(N:ℝ) < η := by
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hηpos
    exact ⟨n + 1, by omega, by simpa using hn⟩
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  -- the vertices and sides
  set w : Fin (N+1) → ℂ := fun k => γ (gtime N k) with hw
  have hm : ∀ k, w k ∈ Ω := fun k => (p (gtime N k)).2
  have hmesh : ∀ k : Fin N, dist (gtime N k.castSucc) (gtime N k.succ) ≤ 1/(N:ℝ) := by
    intro k
    have h1 : ((gtime N k.castSucc : I) : ℝ) = (k:ℝ)/N := gtime_val N _
    have h2 : ((gtime N k.succ : I) : ℝ) = (k:ℝ)/N + 1/N := by
      rw [gtime_val, Fin.val_succ]
      push_cast
      rw [add_div]
    rw [Subtype.dist_eq, Real.dist_eq, h1, h2,
      show (k:ℝ)/N - ((k:ℝ)/N + 1/N) = -(1/N) by ring, abs_neg,
      abs_of_pos (by positivity : (0:ℝ) < 1/(N:ℝ))]
  have hstep : ∀ k : Fin N, dist (w k.castSucc) (w k.succ) < δ := by
    intro k
    have h2 : dist (p (gtime N k.castSucc)) (p (gtime N k.succ)) < δ :=
      hη (lt_of_le_of_lt (hmesh k) hNη)
    have h3 : dist (w k.castSucc) (w k.succ)
        = dist (p (gtime N k.castSucc)) (p (gtime N k.succ)) := by
      show dist (γ (gtime N k.castSucc)) (γ (gtime N k.succ)) = _
      rw [hγ]
      exact (Subtype.dist_eq _ _).symm
    rw [h3]
    exact h2
  have hseg : ∀ k : Fin N, segment ℝ (w k.castSucc) (w k.succ) ⊆ Ω := by
    intro k z hz
    refine hδΩ (w k.castSucc) (Set.mem_range_self _) z ?_
    have hball : segment ℝ (w k.castSucc) (w k.succ) ⊆ Metric.ball (w k.castSucc) δ := by
      refine (convex_ball _ _).segment_subset (by simp [hδpos]) ?_
      rw [Metric.mem_ball, dist_comm]
      exact hstep k
    have hbz := Metric.mem_ball.mp (hball hz)
    rwa [dist_comm] at hbz
  -- the polygonal loop visits `Ω`
  have hPmem : ∀ s : I, polyFun hN w (s:ℝ) ∈ Ω := polyFun_mem hN w hm hseg
  -- the PolyLoop
  have h1 : (⟨w 0, hm 0⟩ : ↥Ω) = x := by
    apply Subtype.ext
    show γ (gtime N 0) = ((x : ↥Ω) : ℂ)
    rw [gtime_zero]
    exact congrArg (fun z : ↥Ω => (z:ℂ)) p.source
  have h2 : (⟨w (Fin.last N), hm _⟩ : ↥Ω) = x := by
    apply Subtype.ext
    show γ (gtime N (Fin.last N)) = ((x : ↥Ω) : ℂ)
    rw [gtime_last hN]
    exact congrArg (fun z : ↥Ω => (z:ℂ)) p.target
  refine ⟨{
    M := N, hM := hN, base := x,
    loop := (polyPath hN w hm hseg).cast h1.symm h2.symm,
    t := gtime N, ht0 := gtime_zero N, ht1 := gtime_last hN,
    htmono := gtime_monotone N,
    haff := ?_ }, ?_⟩
  · intro k u
    rw [Path.cast_coe]
    have h1 : (N:ℝ) * ((gtime N k.castSucc : I) : ℝ) ∈ Icc (k:ℝ) ((k:ℝ)+1) := by
      rw [gtime_val, Fin.val_castSucc]
      have hk : (N:ℝ) * ((k:ℝ)/N) = (k:ℝ) := by field_simp
      exact ⟨le_of_eq hk.symm, by rw [hk]; linarith⟩
    have h2 : (N:ℝ) * ((gtime N k.succ : I) : ℝ) ∈ Icc (k:ℝ) ((k:ℝ)+1) := by
      rw [gtime_val, Fin.val_succ]
      push_cast
      have hk : (N:ℝ) * (((k:ℝ)+1)/N) = (k:ℝ)+1 := by field_simp
      exact ⟨by rw [hk]; linarith, le_of_eq hk⟩
    simp only [polyPath_apply]
    exact polyPath_subpath_coe hN w hm hseg h1 h2 u
  · -- essentiality: the polygonal loop is homotopic to `p`
    intro hcon
    have hFmem : ∀ q : I × I,
        (1 - (q.1:ℝ)) • polyFun hN w (q.2:ℝ) + (q.1:ℝ) • γ q.2 ∈ Ω := by
      rintro ⟨u, t⟩
      obtain ⟨k, hk1, hk2⟩ := gtime_cover hN t
      have hkt : ((t:ℝ) - ((gtime N k.castSucc : I):ℝ)) ≤ 1/(N:ℝ) := by
        have h2' : ((gtime N k.succ : I):ℝ) - ((gtime N k.castSucc : I):ℝ) = 1/(N:ℝ) := by
          rw [gtime_val, gtime_val, Fin.val_castSucc, Fin.val_succ, ← sub_div]
          congr 1; push_cast; ring
        have h3' : (t:ℝ) ≤ ((gtime N k.succ : I):ℝ) := Subtype.coe_le_coe.mpr hk2
        have h4' : ((gtime N k.castSucc : I):ℝ) ≤ (t:ℝ) := Subtype.coe_le_coe.mpr hk1
        linarith
      have htk : dist t (gtime N k.castSucc) ≤ 1/(N:ℝ) := by
        rw [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonneg (by have h := Subtype.coe_le_coe.mpr hk1; linarith : (0:ℝ) ≤ (t:ℝ) - _)]
        exact hkt
      have hγb : dist (γ t) (w k.castSucc) < δ := by
        have hη' := hη (lt_of_le_of_lt htk hNη)
        have h4 : dist (γ t) (w k.castSucc) = dist (p t) (p (gtime N k.castSucc)) := by
          show dist (γ t) (γ (gtime N k.castSucc)) = _
          rw [hγ]
          exact (Subtype.dist_eq _ _).symm
        rw [h4]
        exact hη'
      have hwk : (N:ℝ) * (t:ℝ) ∈ Icc (k:ℝ) ((k:ℝ)+1) := by
        constructor
        · have h := Subtype.coe_le_coe.mpr hk1
          rw [gtime_val, Fin.val_castSucc, div_le_iff₀ hNpos] at h
          linarith
        · have h := Subtype.coe_le_coe.mpr hk2
          rw [gtime_val, Fin.val_succ, le_div_iff₀ hNpos] at h
          push_cast at h; linarith
      have hvextk : vext w (k:ℤ) = w k.castSucc := by
        rw [vext_of_le w k (by omega)]
        congr 1
      have hvextk1 : vext w ((k:ℤ)+1) = w k.succ := by
        rw [show ((k:ℤ)+1) = ((k:ℕ)+1 : ℕ) by push_cast; ring,
          vext_of_le w ((k:ℕ)+1) (by omega)]
        congr 1
      have hPmem : polyFun hN w (t:ℝ) ∈ segment ℝ (w k.castSucc) (w k.succ) := by
        rw [segment_eq_image]
        refine ⟨(N:ℝ) * (t:ℝ) - (k:ℝ), ⟨by linarith [hwk.1], by linarith [hwk.2]⟩, ?_⟩
        rw [polyFun_eq_latSeg_time hN w k (t:ℝ) hwk, latSeg, hvextk, hvextk1]
        module
      have hsegk : ∀ z ∈ segment ℝ (w k.castSucc) (w k.succ), z ∈ Metric.ball (w k.castSucc) δ := by
        refine (convex_ball _ _).segment_subset (by simp [hδpos]) ?_
        rw [Metric.mem_ball, dist_comm]
        exact hstep k
      have hPb : dist (polyFun hN w (t:ℝ)) (w k.castSucc) < δ :=
        Metric.mem_ball.mp (hsegk _ hPmem)
      have hγm : γ t ∈ Metric.ball (w k.castSucc) δ := by rw [Metric.mem_ball]; exact hγb
      have hPm : polyFun hN w (t:ℝ) ∈ Metric.ball (w k.castSucc) δ := hsegk _ hPmem
      refine hδΩ (w k.castSucc) (Set.mem_range_self _) _ ?_
      have hcv : Convex ℝ (Metric.ball (w k.castSucc) δ) := convex_ball _ _
      have hcombo : (1 - (u:ℝ)) • polyFun hN w (t:ℝ) + (u:ℝ) • γ t
          ∈ Metric.ball (w k.castSucc) δ :=
        hcv.segment_subset hPm hγm (by
          rw [segment_eq_image]
          exact ⟨(u:ℝ), ⟨u.2.1, u.2.2⟩, rfl⟩)
      rw [Metric.mem_ball] at hcombo
      rw [dist_comm]
      exact hcombo
    have hmain : (polyPath hN w hm hseg).Homotopic (p.cast h1 h2) := by
      refine ⟨ContinuousMap.HomotopyWith.mk
        (ContinuousMap.Homotopy.mk
          (⟨fun q => (⟨(1 - (q.1:ℝ)) • polyFun hN w (q.2:ℝ) + (q.1:ℝ) • γ q.2,
            hFmem q⟩ : ↥Ω), by
              refine Continuous.subtype_mk ?_ _
              exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
                  ((continuous_polyFun hN w).comp (continuous_subtype_val.comp continuous_snd))).add
                ((continuous_subtype_val.comp continuous_fst).smul (hγc.comp continuous_snd))⟩ :
            C(I × I, ↥Ω))
          (by
            intro t
            apply Subtype.ext
            show (1 - ((0:I):ℝ)) • polyFun hN w (t:ℝ) + ((0:I):ℝ) • γ t
              = ((polyPath hN w hm hseg) t : ℂ)
            rw [show ((0:I):ℝ) = 0 from rfl, sub_zero, one_smul, zero_smul, add_zero,
              polyPath_apply])
          (by
            intro t
            apply Subtype.ext
            show (1 - ((1:I):ℝ)) • polyFun hN w (t:ℝ) + ((1:I):ℝ) • γ t
              = ((p.cast h1 h2) t : ℂ)
            rw [show ((1:I):ℝ) = 1 from rfl, sub_self, zero_smul, one_smul, zero_add]
            simp only [Path.cast_coe, hγ]))
        (by
          intro u t ht
          apply Subtype.ext
          rcases ht with ht | ht
          · rw [ht]
            change (1 - (u:ℝ)) • polyFun hN w (0:ℝ) + (u:ℝ) • γ (0:I)
              = polyFun hN w (0:ℝ)
            rw [polyFun_zero,
              show γ (0:I) = w 0 from by rw [show (0:I) = gtime N 0 from (gtime_zero N).symm]]
            rw [← add_smul, sub_add_cancel, one_smul]
          · rw [Set.mem_singleton_iff.mp ht]
            change (1 - (u:ℝ)) • polyFun hN w (1:ℝ) + (u:ℝ) • γ (1:I)
              = polyFun hN w (1:ℝ)
            rw [polyFun_one,
              show γ (1:I) = w (Fin.last N) from by rw [show (1:I) = gtime N (Fin.last N) from (gtime_last hN).symm]]
            rw [← add_smul, sub_add_cancel, one_smul])⟩
    have hN : ((polyPath hN w hm hseg).cast h1.symm h2.symm).Homotopic
        ((p.cast h1 h2).cast h1.symm h2.symm) :=
      Path.Homotopic.pathCast hmain h1.symm h2.symm
    have happ : ((p.cast h1 h2).cast h1.symm h2.symm) = p := by
      apply Path.ext
      funext t
      simp only [Path.cast_coe]
    rw [happ] at hN
    exact hp ((hcon.symm.trans hN).symm)

/-! ### Descent helpers -/

lemma Icc.convexComb_convexComb (α β x y : I) (u : I) :
    Icc.convexComb (Icc.convexComb α β x) (Icc.convexComb α β y) u
      = Icc.convexComb α β (Icc.convexComb x y u) := by
  apply Subtype.ext
  simp only [Icc.coe_convexComb]
  push_cast
  ring

lemma Icc.exists_convexComb_eq {c d α : I} (h1 : c ≤ α) (h2 : α ≤ d) :
    ∃ s : I, Icc.convexComb c d s = α := by
  by_cases hcd : (c : ℝ) = (d : ℝ)
  · have hcd' : c = d := Subtype.ext hcd
    exact ⟨0, by rw [Icc.convexComb_zero]; exact le_antisymm h1 (h2.trans_eq hcd'.symm)⟩
  · have hcdle : (c : ℝ) ≤ (d : ℝ) := Subtype.coe_le_coe.mpr (h1.trans h2)
    have hlt : (c : ℝ) < (d : ℝ) := lt_of_le_of_ne hcdle hcd
    have hpos : 0 < (d : ℝ) - (c : ℝ) := by linarith
    refine ⟨⟨((α:ℝ) - (c:ℝ)) / ((d:ℝ) - (c:ℝ)), ?_, ?_⟩, ?_⟩
    · rw [div_nonneg_iff]
      left
      exact ⟨sub_nonneg.mpr (Subtype.coe_le_coe.mpr h1), le_of_lt hpos⟩
    · rw [div_le_one hpos]
      have h2' : (α:ℝ) ≤ (d:ℝ) := Subtype.coe_le_coe.mpr h2
      linarith
    · apply Subtype.ext
      rw [Icc.coe_convexComb]
      field_simp
      ring

/-- Affineness on a subinterval. -/
lemma affine_subinterval {G : I → ℂ} {c d : I}
    (hG : ∀ u, G (Icc.convexComb c d u) = (1 - (u:ℝ)) * G c + (u:ℝ) * G d)
    {α β : I} (hc : c ≤ α) (hαβ : α ≤ β) (hβ : β ≤ d) (x : I) :
    G (Icc.convexComb α β x) = (1 - (x:ℝ)) * G α + (x:ℝ) * G β := by
  obtain ⟨s, hs⟩ := Icc.exists_convexComb_eq (c := c) (d := d) hc (hαβ.trans hβ)
  obtain ⟨t, ht⟩ := Icc.exists_convexComb_eq (c := c) (d := d) (hc.trans hαβ) hβ
  have hα : G α = (1 - (s:ℝ)) * G c + (s:ℝ) * G d := by rw [← hs, hG]
  have hβ' : G β = (1 - (t:ℝ)) * G c + (t:ℝ) * G d := by rw [← ht, hG]
  have hmain : G (Icc.convexComb α β x) = (1 - ((Icc.convexComb s t x : I):ℝ)) * G c
      + ((Icc.convexComb s t x : I):ℝ) * G d := by
    rw [show Icc.convexComb α β x = Icc.convexComb (Icc.convexComb c d s)
      (Icc.convexComb c d t) x from by rw [hs, ht], Icc.convexComb_convexComb, hG]
  rw [hmain, hα, hβ', Icc.coe_convexComb]
  push_cast
  ring


/-- The index of a time is monotone. -/
lemma PolyLoop.gidx_mono (L : PolyLoop Ω) {s t : I} (h : s ≤ t) : L.gidx s ≤ L.gidx t := by
  unfold PolyLoop.gidx
  refine Finset.le_max' _ _ ?_
  have hmem := Finset.max'_mem (L.idxSet s) (L.idxSet_nonempty s)
  unfold PolyLoop.idxSet at hmem ⊢
  rw [Finset.mem_filter] at hmem ⊢
  exact ⟨Finset.mem_univ _, hmem.2.trans h⟩

/-- The number of edges of the arc of `L` from `a` to `b`. -/
noncomputable def PolyLoop.arcLen (L : PolyLoop Ω) (a b : I) : ℕ :=
  (L.gidx b : ℕ) - (L.gidx a : ℕ) + (if b = L.t (L.gidx b).castSucc then 0 else 1)

/-- The vertex index of the arc, as a `Fin`. -/
noncomputable def PolyLoop.arck (L : PolyLoop Ω) (a : I) (k : ℕ) : Fin (L.M+1) :=
  if h : (L.gidx a : ℕ) + k ≤ L.M then ⟨(L.gidx a : ℕ) + k, Nat.lt_succ_iff.mpr h⟩ else 0

lemma PolyLoop.arck_val (L : PolyLoop Ω) (a : I) (k : ℕ) (h : (L.gidx a : ℕ) + k ≤ L.M) :
    (L.arck a k : ℕ) = (L.gidx a : ℕ) + k := by
  unfold PolyLoop.arck
  rw [dif_pos h]

/-- The times of the breakpoints of the arc of `L` from `a` to `b`, before rescaling. -/
noncomputable def PolyLoop.arcTau (L : PolyLoop Ω) (a b : I) (hab : a ≤ b)
    (k : Fin (L.arcLen a b + 1)) : I :=
  if (k:ℕ) = 0 then a
  else if (k:ℕ) = L.arcLen a b then b
  else L.t (L.arck a k)

lemma PolyLoop.arck_le (L : PolyLoop Ω) {a b : I} (hab : a ≤ b) {k : ℕ}
    (hk : k ≤ L.arcLen a b - 1) : (L.gidx a : ℕ) + k ≤ L.M := by
  have h1 : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab
  have h2 : (L.gidx b : ℕ) < L.M := (L.gidx b).2
  have h3 : L.arcLen a b - 1 ≤ (L.gidx b : ℕ) - (L.gidx a : ℕ) := by
    unfold PolyLoop.arcLen
    split <;> omega
  omega

lemma PolyLoop.arcLen_pos (L : PolyLoop Ω) {a b : I} (hab : a < b) : 0 < L.arcLen a b := by
  unfold PolyLoop.arcLen
  have hi : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab.le
  split
  · rename_i hb
    by_contra hc
    have h0 : (L.gidx b : ℕ) - (L.gidx a : ℕ) = 0 := by omega
    have heq : (L.gidx a : ℕ) = (L.gidx b : ℕ) := by omega
    have hle : L.t (L.gidx a).castSucc ≤ a := L.gidx_le a
    have he : L.t (L.gidx a).castSucc = b := by
      rw [show L.gidx a = L.gidx b from Fin.ext heq]
      exact hb.symm
    rw [he] at hle
    exact absurd hle (not_le.mpr hab)
  · omega

lemma PolyLoop.arcTau_zero (L : PolyLoop Ω) (a b : I) (hab : a ≤ b) :
    L.arcTau a b hab 0 = a := by
  simp only [PolyLoop.arcTau, Fin.val_zero]
  exact if_pos trivial

lemma PolyLoop.arcTau_last (L : PolyLoop Ω) (a b : I) (hab : a ≤ b)
    (hm : L.arcLen a b ≠ 0) :
    L.arcTau a b hab (Fin.last (L.arcLen a b)) = b := by
  have h1 : ((Fin.last (L.arcLen a b) : Fin (L.arcLen a b + 1)) : ℕ) = L.arcLen a b := by
    simp
  simp only [PolyLoop.arcTau]
  rw [if_neg (by rw [h1]; exact hm), if_pos h1]

lemma PolyLoop.arcTau_mid (L : PolyLoop Ω) (a b : I) (hab : a ≤ b)
    {k : Fin (L.arcLen a b + 1)} (h0 : (k:ℕ) ≠ 0) (hm : (k:ℕ) ≠ L.arcLen a b) :
    L.arcTau a b hab k = L.t (L.arck a k) := by
  simp only [PolyLoop.arcTau]
  rw [if_neg h0, if_neg hm]

lemma PolyLoop.arcTau_le_b (L : PolyLoop Ω) (a b : I) (hab : a ≤ b)
    (k : Fin (L.arcLen a b + 1)) : L.arcTau a b hab k ≤ b := by
  by_cases h0 : (k:ℕ) = 0
  · rw [PolyLoop.arcTau, if_pos h0]; exact hab
  · by_cases hm : (k:ℕ) = L.arcLen a b
    · rw [PolyLoop.arcTau, if_neg h0, if_pos hm]
    · rw [L.arcTau_mid a b hab h0 hm]
      have hk : (k:ℕ) ≤ L.arcLen a b - 1 := by
        have := k.2; omega
      have hbv : (L.arck a k : ℕ) = (L.gidx a : ℕ) + (k:ℕ) := L.arck_val a k (L.arck_le hab hk)
      have h3 : L.arcLen a b - 1 ≤ (L.gidx b : ℕ) - (L.gidx a : ℕ) := by
        unfold PolyLoop.arcLen
        split <;> omega
      have hidx : L.arck a k ≤ (L.gidx b).castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        rw [hbv]; simp only [Fin.val_castSucc]
        omega
      exact (L.htmono hidx).trans (L.gidx_le b)

lemma PolyLoop.arcTau_ge_a (L : PolyLoop Ω) (a b : I) (hab : a ≤ b)
    (k : Fin (L.arcLen a b + 1)) : a ≤ L.arcTau a b hab k := by
  by_cases h0 : (k:ℕ) = 0
  · rw [PolyLoop.arcTau, if_pos h0]
  · by_cases hm : (k:ℕ) = L.arcLen a b
    · rw [PolyLoop.arcTau, if_neg h0, if_pos hm]; exact hab
    · rw [L.arcTau_mid a b hab h0 hm]
      have hk : 1 ≤ (k:ℕ) := by omega
      have hb : (L.gidx a).succ ≤ L.arck a k := by
        apply Fin.le_iff_val_le_val.mpr
        rw [L.arck_val a k (L.arck_le hab (by have := k.2; omega))]
        simp only [Fin.val_succ]
        omega
      exact (le_gidx_succ L a).trans (L.htmono hb)

lemma PolyLoop.arcTau_mono (L : PolyLoop Ω) (a b : I) (hab : a ≤ b) :
    Monotone (L.arcTau a b hab) := by
  intro k k' hkk'
  have hkk'' : (k:ℕ) ≤ (k':ℕ) := hkk'
  by_cases h0 : (k:ℕ) = 0
  · have hk0 : k = 0 := Fin.ext h0
    rw [hk0, L.arcTau_zero a b hab]
    exact L.arcTau_ge_a a b hab k'
  · by_cases h1 : (k':ℕ) = 0
    · exfalso; omega
    · by_cases h2 : (k':ℕ) = L.arcLen a b
      · have hlast : L.arcTau a b hab k' = b := by
          rw [show k' = Fin.last (L.arcLen a b) from Fin.ext h2]
          exact L.arcTau_last a b hab (by omega)
        rw [hlast]
        exact L.arcTau_le_b a b hab k
      · rw [L.arcTau_mid a b hab h0 (by omega), L.arcTau_mid a b hab h1 h2]
        have hidx : L.arck a k ≤ L.arck a k' := by
          apply Fin.le_iff_val_le_val.mpr
          rw [L.arck_val a k (L.arck_le hab (by have := k.2; omega)),
            L.arck_val a k' (L.arck_le hab (by have := k'.2; omega))]
          omega
        exact L.htmono hidx

/-- The rescaled breakpoint times of the arc from `a` to `b`. -/
noncomputable def PolyLoop.subArcT (L : PolyLoop Ω) (a b : I) (hab : a ≤ b) :
    Fin (L.arcLen a b + 1) → I :=
  fun k => ⟨(((L.arcTau a b hab k : I) : ℝ) - (a:ℝ)) / ((b:ℝ) - (a:ℝ)), by
    have hge : (a:ℝ) ≤ (L.arcTau a b hab k : ℝ) :=
      Subtype.coe_le_coe.mpr (L.arcTau_ge_a a b hab k)
    have hle : (L.arcTau a b hab k : ℝ) ≤ (b:ℝ) :=
      Subtype.coe_le_coe.mpr (L.arcTau_le_b a b hab k)
    have hba : (0:ℝ) ≤ (b:ℝ) - (a:ℝ) := by linarith
    refine ⟨div_nonneg (by linarith) hba, ?_⟩
    rcases eq_or_lt_of_le hba with h0 | hpos
    · rw [← h0, div_zero]; norm_num
    · rw [div_le_one hpos]; linarith⟩

lemma PolyLoop.subArcT_conv (L : PolyLoop Ω) (a b : I) (hab : a ≤ b)
    (k : Fin (L.arcLen a b + 1)) :
    Icc.convexComb a b (L.subArcT a b hab k) = L.arcTau a b hab k := by
  have hge : (a:ℝ) ≤ (L.arcTau a b hab k : ℝ) :=
    Subtype.coe_le_coe.mpr (L.arcTau_ge_a a b hab k)
  have hle : (L.arcTau a b hab k : ℝ) ≤ (b:ℝ) :=
    Subtype.coe_le_coe.mpr (L.arcTau_le_b a b hab k)
  apply Subtype.ext
  show (1 - (((L.arcTau a b hab k : I) : ℝ) - (a:ℝ)) / ((b:ℝ) - (a:ℝ))) * (a:ℝ)
      + ((((L.arcTau a b hab k : I) : ℝ) - (a:ℝ)) / ((b:ℝ) - (a:ℝ))) * (b:ℝ)
      = ((L.arcTau a b hab k : I) : ℝ)
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ (b:ℝ) - (a:ℝ) by linarith) with h0 | hpos
  · have hba : (b:ℝ) = (a:ℝ) := by linarith
    have heq : L.arcTau a b hab k = a :=
      le_antisymm ((L.arcTau_le_b a b hab k).trans (le_of_eq (Subtype.ext hba)))
        (L.arcTau_ge_a a b hab k)
    rw [← h0, div_zero, zero_mul, sub_zero, one_mul, add_zero, heq]
  · field_simp
    ring

lemma PolyLoop.subArcT_mono (L : PolyLoop Ω) (a b : I) (hab : a ≤ b) :
    Monotone (L.subArcT a b hab) := by
  intro k k' hkk'
  have hmono : L.arcTau a b hab k ≤ L.arcTau a b hab k' := L.arcTau_mono a b hab hkk'
  have hc : (a:ℝ) ≤ (b:ℝ) := Subtype.coe_le_coe.mpr hab
  show (((L.arcTau a b hab k : I) : ℝ) - (a:ℝ)) / ((b:ℝ) - (a:ℝ))
      ≤ (((L.arcTau a b hab k' : I) : ℝ) - (a:ℝ)) / ((b:ℝ) - (a:ℝ))
  rcases eq_or_lt_of_le (show (0:ℝ) ≤ (b:ℝ) - (a:ℝ) by linarith) with h0 | hpos
  · rw [← h0, div_zero, div_zero]
  · exact div_le_div_of_nonneg_right
      (sub_le_sub_right (Subtype.coe_le_coe.mpr hmono) _) (le_of_lt hpos)

lemma PolyLoop.arcLen_le (L : PolyLoop Ω) (a b : I) :
    L.arcLen a b ≤ (L.gidx b : ℕ) - (L.gidx a : ℕ) + 1 := by
  unfold PolyLoop.arcLen
  split <;> omega

lemma PolyLoop.arcLen_ge (L : PolyLoop Ω) (a b : I) :
    (L.gidx b : ℕ) - (L.gidx a : ℕ) ≤ L.arcLen a b := by
  unfold PolyLoop.arcLen
  split <;> omega

/-- The `Fin L.M` index of the arc (used for the last interval). -/
noncomputable def PolyLoop.arckM (L : PolyLoop Ω) (a : I) (k : ℕ) : Fin L.M :=
  if h : (L.gidx a : ℕ) + k < L.M then ⟨(L.gidx a : ℕ) + k, h⟩ else ⟨0, L.hM⟩

lemma PolyLoop.arckM_val (L : PolyLoop Ω) (a : I) (k : ℕ)
    (h : (L.gidx a : ℕ) + k < L.M) : (L.arckM a k : ℕ) = (L.gidx a : ℕ) + k := by
  unfold PolyLoop.arckM
  rw [dif_pos h]

/-- First-interval bound. -/
lemma PolyLoop.arcTau_succ_le (L : PolyLoop Ω) {a b : I} (hab : a ≤ b)
    {k : Fin (L.arcLen a b)} (h0 : (k:ℕ) = 0) :
    L.arcTau a b hab k.succ ≤ L.t (L.gidx a).succ := by
  have h1 : ((k.succ : Fin (L.arcLen a b + 1)) : ℕ) = 1 := by
    simp only [Fin.val_succ]; omega
  have hgk : 1 ≤ L.arcLen a b := by have := k.2; omega
  rcases lt_or_eq_of_le hgk with hlt | heq
  · have hk_le : ↑(k.succ : Fin (L.arcLen a b + 1)) ≤ L.arcLen a b - 1 := by rw [h1]; omega
    rw [L.arcTau_mid a b hab (by rw [h1]; omega) (by rw [h1]; omega)]
    refine L.htmono (Fin.le_iff_val_le_val.mpr ?_)
    rw [L.arck_val a ↑(k.succ : Fin (L.arcLen a b + 1)) (L.arck_le hab hk_le)]
    simp only [Fin.val_succ]
    omega
  · have hj' : k.succ = Fin.last (L.arcLen a b) := by
      apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega
    rw [hj', L.arcTau_last a b hab (by omega)]
    have hge : L.gidx a ≤ L.gidx b := L.gidx_mono hab
    have hgb : (L.gidx b : ℕ) ≤ (L.gidx a : ℕ) + 1 := by
      have h := L.arcLen_ge a b
      omega
    rcases eq_or_lt_of_le hge with he | hlt'
    · have hbl : b ≤ L.t (L.gidx b).succ := le_gidx_succ L b
      rw [← he] at hbl
      exact hbl
    · have hgb' : (L.gidx b : ℕ) = (L.gidx a : ℕ) + 1 := by
        have h1' : (L.gidx a : ℕ) < (L.gidx b : ℕ) := hlt'
        omega
      have hd : b = L.t (L.gidx b).castSucc := by
        unfold PolyLoop.arcLen at heq
        split_ifs at heq with hb
        · exact hb
        · have h1' : (L.gidx a : ℕ) < (L.gidx b : ℕ) := hlt'
          omega
      rw [hd]
      refine L.htmono (Fin.le_iff_val_le_val.mpr ?_)
      simp only [Fin.val_castSucc, Fin.val_succ]
      omega

/-- Last interval, left endpoint. -/
lemma PolyLoop.arcTau_last_left (L : PolyLoop Ω) {a b : I} (hab : a ≤ b)
    {k : Fin (L.arcLen a b)} (h0 : (k:ℕ) ≠ 0) (hm : (k:ℕ) + 1 = L.arcLen a b)
    (hle : (L.gidx a : ℕ) + (k:ℕ) < L.M) :
    L.arcTau a b hab k.castSucc = L.t (L.arckM a ↑k).castSucc := by
  have hkm : (k:ℕ) ≠ L.arcLen a b := by omega
  have hk_le : ↑(k.castSucc : Fin (L.arcLen a b + 1)) ≤ L.arcLen a b - 1 := by
    simp only [Fin.val_castSucc]; omega
  rw [L.arcTau_mid a b hab h0 hkm]
  congr 1
  apply Fin.ext
  rw [L.arck_val a ↑(k.castSucc : Fin (L.arcLen a b + 1)) (L.arck_le hab hk_le),
    Fin.val_castSucc, Fin.val_castSucc, L.arckM_val a ↑k hle]

/-- Last interval, right endpoint. -/
lemma PolyLoop.arcTau_last_right (L : PolyLoop Ω) {a b : I} (hab : a ≤ b)
    {k : Fin (L.arcLen a b)} (hm : (k:ℕ) + 1 = L.arcLen a b)
    (hle : (L.gidx a : ℕ) + (k:ℕ) < L.M) :
    b ≤ L.t (L.arckM a ↑k).succ := by
  by_cases hb : b = L.t (L.gidx b).castSucc
  · have hge : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab
    have hh : L.arcLen a b = (L.gidx b : ℕ) - (L.gidx a : ℕ) + 0 := by
      unfold PolyLoop.arcLen
      rw [if_pos hb]
    have hidx : (L.arckM a ↑k).succ = (L.gidx b).castSucc := by
      apply Fin.ext
      rw [Fin.val_succ, L.arckM_val a ↑k hle, Fin.val_castSucc]
      omega
    rw [hidx]
    exact le_of_eq hb
  · have harc : L.arcLen a b = (L.gidx b : ℕ) - (L.gidx a : ℕ) + 1 := by
      unfold PolyLoop.arcLen
      rw [if_neg hb]
    have hb1 : b ≤ L.t (L.gidx b).succ := le_gidx_succ L b
    have hge : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab
    have hidx : (L.arckM a ↑k).succ = (L.gidx b).succ := by
      apply Fin.ext
      rw [Fin.val_succ, L.arckM_val a ↑k hle, Fin.val_succ]
      omega
    rwa [hidx]

/-- **Affineness of the loop between two consecutive arc breakpoints.** -/
lemma PolyLoop.arcTau_affine (L : PolyLoop Ω) {a b : I} (hab : a ≤ b)
    (k : Fin (L.arcLen a b)) (x : I) :
    ((L.loop (Icc.convexComb (L.arcTau a b hab k.castSucc) (L.arcTau a b hab k.succ) x)
      : ↥Ω) : ℂ)
      = (1 - (x:ℝ)) * ((L.loop (L.arcTau a b hab k.castSucc) : ↥Ω) : ℂ)
        + (x:ℝ) * ((L.loop (L.arcTau a b hab k.succ) : ↥Ω) : ℂ) := by
  by_cases h0 : (k:ℕ) = 0
  · have hj : k.castSucc = 0 := Fin.ext h0
    rw [hj, L.arcTau_zero a b hab]
    have hα : L.t (L.gidx a).castSucc ≤ a := L.gidx_le a
    have hzero : (0 : Fin (L.arcLen a b + 1)) ≤ k.succ :=
      Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
    have hαβ : a ≤ L.arcTau a b hab k.succ := by
      have hh := L.arcTau_mono a b hab hzero
      rwa [L.arcTau_zero a b hab] at hh
    exact affine_subinterval (G := fun u => ((L.loop u : ↥Ω) : ℂ))
      (fun u => L.haff (L.gidx a) u) hα hαβ (L.arcTau_succ_le hab h0) x
  · by_cases hm : (k:ℕ) + 1 = L.arcLen a b
    · have hj' : k.succ = Fin.last (L.arcLen a b) := by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega
      have hm0 : L.arcLen a b ≠ 0 := by omega
      rw [hj', L.arcTau_last a b hab hm0]
      have h0' : (k:ℕ) ≠ 0 := by intro h; omega
      have hle : (L.gidx a : ℕ) + (k:ℕ) < L.M := by
        have h1 : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab
        have h2 : (L.gidx b : ℕ) < L.M := (L.gidx b).2
        have h3 := L.arcLen_le a b
        omega
      have hleft := L.arcTau_last_left hab h0' hm hle
      have hright := L.arcTau_last_right hab hm hle
      exact affine_subinterval (G := fun u => ((L.loop u : ↥Ω) : ℂ))
        (α := L.arcTau a b hab k.castSucc) (β := b)
        (fun u => L.haff (L.arckM a ↑k) u)
        (le_of_eq hleft.symm) (L.arcTau_le_b a b hab k.castSucc) hright x
    · have hk1 : (k:ℕ) ≠ 0 := by intro h; omega
      have hkm : (k:ℕ) ≠ L.arcLen a b := by intro h; omega
      have hk_le : (k:ℕ) ≤ L.arcLen a b - 1 := by have := k.2; omega
      have hk'_le : ↑(k.succ : Fin (L.arcLen a b + 1)) ≤ L.arcLen a b - 1 := by
        simp only [Fin.val_succ]; omega
      have hle : (L.gidx a : ℕ) + (k:ℕ) < L.M := by
        have h1 : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab
        have h2 : (L.gidx b : ℕ) < L.M := (L.gidx b).2
        have h3 := L.arcLen_le a b
        omega
      have hp : L.arck a ↑(k.castSucc : Fin (L.arcLen a b + 1))
          = (⟨(L.gidx a : ℕ) + (k:ℕ), hle⟩ : Fin L.M).castSucc := by
        apply Fin.ext
        rw [L.arck_val a ↑(k.castSucc : Fin (L.arcLen a b + 1)) (L.arck_le hab hk_le)]
        simp only [Fin.val_castSucc, Fin.val_mk]
      have hp' : L.arck a ↑(k.succ : Fin (L.arcLen a b + 1))
          = (⟨(L.gidx a : ℕ) + (k:ℕ), hle⟩ : Fin L.M).succ := by
        apply Fin.ext
        rw [L.arck_val a ↑(k.succ : Fin (L.arcLen a b + 1)) (L.arck_le hab hk'_le)]
        simp only [Fin.val_succ, Fin.val_mk]
        omega
      have hk'1 : ((k.succ : Fin (L.arcLen a b + 1)) : ℕ) ≠ 0 := by
        intro h; rw [Fin.val_succ] at h; omega
      have hk'm : ((k.succ : Fin (L.arcLen a b + 1)) : ℕ) ≠ L.arcLen a b := by
        intro h; rw [Fin.val_succ] at h; exact hm h
      rw [L.arcTau_mid a b hab hk1 hkm, L.arcTau_mid a b hab hk'1 hk'm, hp, hp']
      exact L.haff ⟨(L.gidx a : ℕ) + (k:ℕ), hle⟩ x

lemma PolyLoop.subArcT_zero (L : PolyLoop Ω) {a b : I} (hab : a < b) :
    L.subArcT a b hab.le 0 = 0 := by
  apply Subtype.ext
  show ((((L.arcTau a b hab.le 0 : I) : ℝ) - (a:ℝ)) / ((b:ℝ) - (a:ℝ))) = ((0:I):ℝ)
  rw [L.arcTau_zero a b hab.le]
  norm_num

lemma PolyLoop.subArcT_last (L : PolyLoop Ω) {a b : I} (hab : a < b) :
    L.subArcT a b hab.le (Fin.last (L.arcLen a b)) = 1 := by
  apply Subtype.ext
  show ((((L.arcTau a b hab.le (Fin.last (L.arcLen a b)) : I) : ℝ) - (a:ℝ))
      / ((b:ℝ) - (a:ℝ))) = (1:ℝ)
  rw [L.arcTau_last a b hab.le (ne_of_gt (L.arcLen_pos hab))]
  have hba : (b:ℝ) ≠ (a:ℝ) := by
    have := Subtype.coe_lt_coe.mpr hab
    linarith
  field_simp

/-- **The arc of a polygonal loop is a polygonal loop.** -/
noncomputable def PolyLoop.subArc (L : PolyLoop Ω) {a b : I} (hab : a < b)
    (hval : L.loop a = L.loop b) : PolyLoop Ω where
  M := L.arcLen a b
  hM := L.arcLen_pos hab
  base := L.loop a
  loop := (L.loop.subpath a b).cast rfl hval
  t := L.subArcT a b hab.le
  ht0 := L.subArcT_zero hab
  ht1 := L.subArcT_last hab
  htmono := L.subArcT_mono a b hab.le
  haff := by
    intro k x
    simp only [Path.cast_coe]
    have hL : ∀ j : Fin (L.arcLen a b + 1),
        (((L.loop.subpath a b) (L.subArcT a b hab.le j) : ↥Ω) : ℂ)
          = ((L.loop (L.arcTau a b hab.le j) : ↥Ω) : ℂ) := by
      intro j
      show ((L.loop (Icc.convexComb a b (L.subArcT a b hab.le j)) : ↥Ω) : ℂ) = _
      rw [L.subArcT_conv a b hab.le j]
    have hgoal := L.arcTau_affine hab.le k x
    have hfin : ((L.loop (Icc.convexComb a b
        (Icc.convexComb (L.subArcT a b hab.le k.castSucc) (L.subArcT a b hab.le k.succ) x))
        : ↥Ω) : ℂ)
        = (1 - (x:ℝ)) * ((L.loop (L.arcTau a b hab.le k.castSucc) : ↥Ω) : ℂ)
          + (x:ℝ) * ((L.loop (L.arcTau a b hab.le k.succ) : ↥Ω) : ℂ) := by
      rw [← Icc.convexComb_convexComb a b (L.subArcT a b hab.le k.castSucc)
          (L.subArcT a b hab.le k.succ) x,
        L.subArcT_conv a b hab.le k.castSucc, L.subArcT_conv a b hab.le k.succ]
      exact hgoal
    rw [hL k.castSucc, hL k.succ]
    show ((L.loop (Icc.convexComb a b
        (Icc.convexComb (L.subArcT a b hab.le k.castSucc) (L.subArcT a b hab.le k.succ) x))
        : ↥Ω) : ℂ)
        = (1 - (x:ℝ)) * ((L.loop (L.arcTau a b hab.le k.castSucc) : ↥Ω) : ℂ)
          + (x:ℝ) * ((L.loop (L.arcTau a b hab.le k.succ) : ↥Ω) : ℂ)
    exact hfin

/-- The complementary arc, from `b` around the base point back to `a`. -/
noncomputable def PolyLoop.wrapPath (L : PolyLoop Ω) (a b : I) : Path (L.loop b) (L.loop a) :=
  ((L.loop.subpath b 1).cast rfl (L.loop.source'.trans L.loop.target'.symm)).trans
    (L.loop.subpath 0 a)

lemma PolyLoop.wrapPath_coe (L : PolyLoop Ω) (a b : I) (t : I) :
    ((L.wrapPath a b) t : ↥Ω) = (L.wrapPath a b) t := rfl

/-- The complementary arc as a loop at `L.loop a`, when `L.loop a = L.loop b`. -/
noncomputable def PolyLoop.wrapLoop (L : PolyLoop Ω) (a b : I) (hval : L.loop a = L.loop b) :
    Path (L.loop a) (L.loop a) :=
  ((L.loop.subpath b 1).cast hval L.loop.target'.symm).trans
    ((L.loop.subpath 0 a).cast L.loop.source'.symm rfl)

/-- Endpoint-fixing casts are the identity. -/
lemma Path.cast_rfl_rfl {Y : Type*} [TopologicalSpace Y] {x y : Y} (γ : Path x y) :
    γ.cast rfl rfl = γ := by
  ext t
  rfl

/-- Casting a concatenation at the two outer endpoints. -/
lemma Path.cast_trans' {Y : Type*} [TopologicalSpace Y] {a b c a' c' : Y}
    (γ : Path a b) (δ : Path b c) (hx : a' = a) (hy : c' = c) :
    (γ.trans δ).cast hx hy = (γ.cast hx rfl).trans (δ.cast rfl hy) := by
  ext t
  rw [Path.trans_apply]
  rw [show ((γ.trans δ).cast hx hy) t = (γ.trans δ) t from rfl, Path.trans_apply]
  split_ifs <;> rfl

/-- **Step (1)-(4) of the dichotomy**: if the sub-arc `[a,b]` is null-homotopic then
`L.loop.subpath a 1` is homotopic to `(L.loop.subpath b 1)` cast to start at `L.loop a`. -/
lemma PolyLoop.subpath_one_homotopic_cast (L : PolyLoop Ω) {a b : I} (hval : L.loop a = L.loop b)
    (hA : (L.loop.subpath a b).Homotopic ((Path.refl (L.loop a)).cast rfl hval.symm)) :
    (L.loop.subpath a 1).Homotopic ((L.loop.subpath b 1).cast hval rfl) := by
  have hC : (Path.refl (L.loop a)).cast rfl hval.symm
      = (Path.refl (L.loop b)).cast hval rfl := by
    ext t
    rw [Path.cast_coe, Path.cast_coe]
    exact congrArg (fun z : ↥Ω => (z : ℂ)) hval
  have h1 : ((L.loop.subpath a b).trans (L.loop.subpath b 1)).Homotopic
      (((Path.refl (L.loop a)).cast rfl hval.symm).trans (L.loop.subpath b 1)) :=
    Path.Homotopic.hcomp hA (Path.Homotopic.refl _)
  have h2 : (((Path.refl (L.loop b)).cast hval rfl).trans (L.loop.subpath b 1)).Homotopic
      ((L.loop.subpath b 1).cast hval rfl) := by
    have heq : ((L.loop.subpath b 1).cast rfl rfl) = (L.loop.subpath b 1) :=
      Path.cast_rfl_rfl _
    refine (Path.Homotopic.pathCast
      (Path.Homotopic.refl_trans (L.loop.subpath b 1)) hval rfl).trans ?_
    rw [← heq]
  have h3 : ((L.loop.subpath a b).trans (L.loop.subpath b 1)).Homotopic (L.loop.subpath a 1) :=
    ⟨Path.Homotopy.subpathTransSubpath L.loop a b 1⟩
  rw [hC] at h1
  exact h3.symm.trans (h1.trans h2)

/-- `subpath 0 1` is the loop with the endpoint casts. -/
lemma PolyLoop.subpath_zero_one' (L : PolyLoop Ω) :
    L.loop.subpath 0 1 = L.loop.cast L.loop.source' L.loop.target' := by
  ext t
  rw [Path.cast_coe]
  show ((L.loop (Icc.convexComb (0:I) 1 t) : ↥Ω) : ℂ) = ((L.loop t : ↥Ω) : ℂ)
  rw [Icc.convexComb_zero_one]

/-- Two endpoint casts cancel against the identity casts. -/
lemma PolyLoop.cast_cancel (L : PolyLoop Ω) :
    (L.loop.cast L.loop.source' L.loop.target').cast L.loop.source'.symm
      L.loop.target'.symm = L.loop := by
  ext t
  rfl

/-- A cast with `rfl` inserted in the middle. -/
lemma Path.cast_rfl_mid {Y : Type*} [TopologicalSpace Y] {a b a' b' : Y}
    (γ : Path a b) (hx : a' = a) (hy : b' = b) :
    (γ.cast hx rfl).cast rfl hy = γ.cast hx hy := by
  ext t
  rfl

/-- **Steps (5)-(10) of the dichotomy**: from the null-homotopy of the sub-arc `[a,b]` we get
`L.loop` homotopic to the concatenation `Pc.trans Qc` of the two half-arcs, cast to a loop. -/
lemma PolyLoop.loop_homotopic_cast_trans (L : PolyLoop Ω) {a b : I} (hval : L.loop a = L.loop b)
    (hA : (L.loop.subpath a b).Homotopic ((Path.refl (L.loop a)).cast rfl hval.symm)) :
    L.loop.Homotopic
      (((L.loop.subpath 0 a).cast L.loop.source'.symm rfl).trans
        ((L.loop.subpath b 1).cast hval L.loop.target'.symm)) := by
  have h5 := L.subpath_one_homotopic_cast hval hA
  have h6 : ((L.loop.subpath 0 a).trans (L.loop.subpath a 1)).Homotopic (L.loop.subpath 0 1) :=
    ⟨Path.Homotopy.subpathTransSubpath L.loop 0 a 1⟩
  have h7 : ((L.loop.subpath 0 a).trans (L.loop.subpath a 1)).Homotopic
      ((L.loop.subpath 0 a).trans ((L.loop.subpath b 1).cast hval rfl)) :=
    Path.Homotopic.hcomp (Path.Homotopic.refl _) h5
  have h8 : (L.loop.subpath 0 1).Homotopic
      ((L.loop.subpath 0 a).trans ((L.loop.subpath b 1).cast hval rfl)) := h6.symm.trans h7
  have h9 := Path.Homotopic.pathCast h8 L.loop.source'.symm L.loop.target'.symm
  rw [L.subpath_zero_one'] at h9
  rw [L.cast_cancel] at h9
  rw [Path.cast_trans' (L.loop.subpath 0 a) ((L.loop.subpath b 1).cast hval rfl)
    L.loop.source'.symm L.loop.target'.symm] at h9
  rw [Path.cast_rfl_mid] at h9
  exact h9

/-- **Conjugation**: a loop `P.trans Q` at `u` is null-homotopic as soon as the complementary
loop `Q.trans P` at `v` is. -/
lemma Path.Homotopic.trans_of_conj {Y : Type*} [TopologicalSpace Y] {u v : Y}
    (P : Path u v) (Q : Path v u) (h : (Q.trans P).Homotopic (Path.refl v)) :
    (P.trans Q).Homotopic (Path.refl u) := by
  have hPP : (P.trans P.symm).Homotopic (Path.refl u) := Path.Homotopic.trans_symm P
  have h1 : (P.trans Q).Homotopic ((P.trans Q).trans (P.trans P.symm)) :=
    (Path.Homotopic.trans_refl (P.trans Q)).symm.trans
      (Path.Homotopic.hcomp (Path.Homotopic.refl (P.trans Q)) hPP.symm)
  have h2 : ((P.trans Q).trans (P.trans P.symm)).Homotopic (((P.trans Q).trans P).trans P.symm) :=
    (Path.Homotopic.trans_assoc (P.trans Q) P P.symm).symm
  have h3 : (((P.trans Q).trans P).trans P.symm).Homotopic
      ((P.trans (Q.trans P)).trans P.symm) :=
    Path.Homotopic.hcomp (Path.Homotopic.trans_assoc P Q P) (Path.Homotopic.refl P.symm)
  have h4 : ((P.trans (Q.trans P)).trans P.symm).Homotopic
      ((P.trans (Path.refl v)).trans P.symm) :=
    Path.Homotopic.hcomp (Path.Homotopic.hcomp (Path.Homotopic.refl P) h)
      (Path.Homotopic.refl P.symm)
  have h5 : ((P.trans (Path.refl v)).trans P.symm).Homotopic (P.trans P.symm) :=
    Path.Homotopic.hcomp (Path.Homotopic.trans_refl P) (Path.Homotopic.refl P.symm)
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans hPP))))

/-- **The dichotomy**: if the sub-arc `[a,b]` of a polygonal loop is null-homotopic, then the
complementary (wrapping) arc is *essential*. -/
theorem PolyLoop.not_nullhomotopic_wrapLoop_of_nullhomotopic_subArc (L : PolyLoop Ω) {a b : I}
    (hval : L.loop a = L.loop b)
    (hA : (L.loop.subpath a b).Homotopic ((Path.refl (L.loop a)).cast rfl hval.symm))
    (hL : L.Essential) :
    ¬ (L.wrapLoop a b hval).Homotopic (Path.refl (L.loop a)) := by
  intro hW
  have hmain := L.loop_homotopic_cast_trans hval hA
  exact hL (hmain.trans (Path.Homotopic.trans_of_conj
    ((L.loop.subpath 0 a).cast L.loop.source'.symm rfl)
    ((L.loop.subpath b 1).cast hval L.loop.target'.symm) hW))

/-- Casting a path to new endpoints and back is the identity. -/
lemma Path.cast_cast_self {Y : Type*} [TopologicalSpace Y] {a b a' b' : Y}
    (γ : Path a b) (hx : a' = a) (hy : b' = b) :
    (γ.cast hx hy).cast hx.symm hy.symm = γ := by
  ext t
  rw [Path.cast_coe, Path.cast_coe]

/-- `Path.cast` is injective on homotopy classes. -/
lemma Path.Homotopic.cast_iff {Y : Type*} [TopologicalSpace Y] {a b a' b' : Y}
    {γ δ : Path a b} (hx : a' = a) (hy : b' = b) :
    (γ.cast hx hy).Homotopic (δ.cast hx hy) ↔ γ.Homotopic δ := by
  refine ⟨fun h => ?_, fun h => Path.Homotopic.pathCast h hx hy⟩
  have h1 := Path.Homotopic.pathCast h hx.symm hy.symm
  rwa [Path.cast_cast_self γ hx hy, Path.cast_cast_self δ hx hy] at h1

/-- **The dichotomy, in the form used by the descent**: for a double point `(a,b)` of an essential
polygonal loop, either the arc `[a,b]` is essential or the complementary (wrapping) arc is. -/
theorem PolyLoop.essential_or_wrap_of_double_point (L : PolyLoop Ω) (hL : L.Essential) {a b : I}
    (hval : L.loop a = L.loop b) :
    (¬ (L.loop.subpath a b).Homotopic ((Path.refl (L.loop a)).cast rfl hval.symm))
      ∨ ¬ (L.wrapLoop a b hval).Homotopic (Path.refl (L.loop a)) := by
  by_cases hA : (L.loop.subpath a b).Homotopic ((Path.refl (L.loop a)).cast rfl hval.symm)
  · exact Or.inr (L.not_nullhomotopic_wrapLoop_of_nullhomotopic_subArc hval hA hL)
  · exact Or.inl hA

lemma PolyLoop.t_le_one (L : PolyLoop Ω) (m : Fin (L.M+1)) : L.t m ≤ 1 := by
  have h : m ≤ Fin.last L.M :=
    Fin.le_iff_val_le_val.mpr (by rw [Fin.val_last]; exact Nat.lt_succ_iff.mp m.2)
  rw [← L.ht1]
  exact L.htmono h

lemma PolyLoop.zero_le_t (L : PolyLoop Ω) (m : Fin (L.M+1)) : 0 ≤ L.t m := by
  have h : (0 : Fin (L.M+1)) ≤ m := Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
  rw [← L.ht0]
  exact L.htmono h

/-- The parameter of the time `L.t m` inside `[b,1]`. -/
noncomputable def PolyLoop.wrapS (L : PolyLoop Ω) (b : I) (m : Fin (L.M+1))
    (hb : b ≤ L.t m) : I :=
  (Icc.exists_convexComb_eq (c := b) (d := 1) (α := L.t m) hb (L.t_le_one m)).choose

lemma PolyLoop.wrapS_spec (L : PolyLoop Ω) (b : I) (m : Fin (L.M+1)) (hb : b ≤ L.t m) :
    Icc.convexComb b 1 (L.wrapS b m hb) = L.t m :=
  (Icc.exists_convexComb_eq (c := b) (d := 1) (α := L.t m) hb (L.t_le_one m)).choose_spec

/-- The parameter of the time `L.t m` inside `[0,a]`. -/
noncomputable def PolyLoop.wrapS0 (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1))
    (hm : L.t m ≤ a) : I :=
  (Icc.exists_convexComb_eq (c := 0) (d := a) (α := L.t m) (L.zero_le_t m) hm).choose

lemma PolyLoop.wrapS0_spec (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1)) (hm : L.t m ≤ a) :
    Icc.convexComb 0 a (L.wrapS0 a m hm) = L.t m :=
  (Icc.exists_convexComb_eq (c := 0) (d := a) (α := L.t m) (L.zero_le_t m) hm).choose_spec

/-- Number of wrap breakpoints lying in the interval `(b,1)`. -/
noncomputable def PolyLoop.wrapNB (L : PolyLoop Ω) (b : I) : ℕ :=
  L.M - 1 - (L.gidx b : ℕ)

/-- Number of wrap breakpoints lying in the interval `(0,a)`. -/
noncomputable def PolyLoop.wrapNC (L : PolyLoop Ω) (a : I) : ℕ :=
  if (L.gidx a : ℕ) = 0 then 0
  else (L.gidx a : ℕ) - 1 + (if a = L.t (L.gidx a).castSucc then 0 else 1)

/-- The number of edges of the wrapping arc. -/
noncomputable def PolyLoop.wrapM (L : PolyLoop Ω) (a b : I) : ℕ :=
  2 + L.wrapNB b + L.wrapNC a

lemma PolyLoop.wrapNC_le (L : PolyLoop Ω) (a : I) : L.wrapNC a ≤ (L.gidx a : ℕ) := by
  unfold PolyLoop.wrapNC
  split_ifs <;> omega

lemma PolyLoop.gidx_add_le (L : PolyLoop Ω) (b : I) {k : ℕ} (hk : k ≤ L.wrapNB b) :
    (L.gidx b : ℕ) + k ≤ L.M := by
  unfold PolyLoop.wrapNB at hk
  have h : (L.gidx b : ℕ) ≤ L.M - 1 := by have := (L.gidx b).2; omega
  omega

/-- Block A side condition: for `m` at least `gidx b + 1`, the time `L.t m` is at least `b`. -/
lemma PolyLoop.le_t_of_gidx_le (L : PolyLoop Ω) (b : I) {m : ℕ}
    (hm : (L.gidx b : ℕ) + 1 ≤ m) (hm' : m ≤ L.M) : b ≤ L.t ⟨m, by omega⟩ := by
  have h1 : b ≤ L.t (L.gidx b).succ := le_gidx_succ L b
  have h2 : (L.gidx b).succ ≤ (⟨m, by omega⟩ : Fin (L.M+1)) := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_succ, Fin.val_mk]
    omega
  exact h1.trans (L.htmono h2)

/-- Block C side condition: for `m ≤ wrapNC a`, the time `L.t m` is at most `a`. -/
lemma PolyLoop.t_le_a_of_wrapNC (L : PolyLoop Ω) (a : I) {m : ℕ} (hm : m ≤ L.wrapNC a)
    (hm' : m ≤ L.M) : L.t ⟨m, by omega⟩ ≤ a := by
  have h1 : L.t (L.gidx a).castSucc ≤ a := L.gidx_le a
  have h2 : m ≤ (L.gidx a : ℕ) := hm.trans (L.wrapNC_le a)
  have h3 : (⟨m, by omega⟩ : Fin (L.M+1)) ≤ (L.gidx a).castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    simp only [Fin.val_castSucc, Fin.val_mk]
    exact h2
  exact (L.htmono h3).trans h1

/-- Parameter of a block-A breakpoint (already rescaled to the first half). -/
noncomputable def PolyLoop.wrapTA (L : PolyLoop Ω) (b : I) (m : Fin (L.M+1))
    (hb : b ≤ L.t m) : I :=
  ⟨(((L.wrapS b m hb : I) : ℝ)) / 2, by
    have hx := (L.wrapS b m hb).2
    constructor <;> linarith [hx.1, hx.2]⟩

/-- Parameter of a block-C breakpoint (rescaled to the second half). -/
noncomputable def PolyLoop.wrapTC (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1))
    (hm : L.t m ≤ a) : I :=
  ⟨(1 + ((L.wrapS0 a m hm : I) : ℝ)) / 2, by
    have hx := (L.wrapS0 a m hm).2
    constructor <;> linarith [hx.1, hx.2]⟩

/-- The breakpoint times of the wrapping arc. -/
noncomputable def PolyLoop.wrapT (L : PolyLoop Ω) (a b : I) : Fin (L.wrapM a b + 1) → I :=
  fun k =>
    if h0 : (k:ℕ) = 0 then 0
    else if h1 : (k:ℕ) ≤ L.wrapNB b then
      L.wrapTA b ⟨(L.gidx b : ℕ) + k, by
          have h := L.gidx_add_le b h1
          omega⟩ (by
        refine L.le_t_of_gidx_le b ?_ ?_
        · omega
        · have h := L.gidx_add_le b h1
          omega)
    else if h2 : (k:ℕ) = L.wrapNB b + 1 then ⟨1 / 2, by norm_num⟩
    else if h3 : (k:ℕ) ≤ L.wrapNB b + 1 + L.wrapNC a then
      L.wrapTC a ⟨(k:ℕ) - L.wrapNB b - 1, by
          have h := L.wrapNC_le a
          have h4 : (L.gidx a : ℕ) < L.M := (L.gidx a).2
          omega⟩ (by
        refine L.t_le_a_of_wrapNC a ?_ ?_
        · have h := L.wrapNC_le a
          omega
        · have h := L.wrapNC_le a
          have h4 : (L.gidx a : ℕ) < L.M := (L.gidx a).2
          omega)
    else 1

lemma PolyLoop.wrapT_zero (L : PolyLoop Ω) (a b : I) : L.wrapT a b 0 = 0 := by
  unfold PolyLoop.wrapT
  rw [dif_pos (show (((0 : Fin (L.wrapM a b + 1)) : ℕ)) = 0 from rfl)]

lemma PolyLoop.wrapT_last (L : PolyLoop Ω) (a b : I) :
    L.wrapT a b (Fin.last (L.wrapM a b)) = 1 := by
  have hM : (((Fin.last (L.wrapM a b)) : Fin (L.wrapM a b + 1)) : ℕ) = L.wrapM a b := by simp
  have hdef : L.wrapM a b = 2 + L.wrapNB b + L.wrapNC a := rfl
  unfold PolyLoop.wrapT
  rw [dif_neg (by rw [hM]; omega), dif_neg (by rw [hM, hdef]; omega),
    dif_neg (by rw [hM, hdef]; omega), dif_neg (by rw [hM, hdef]; omega)]

/-! #### The values of `wrapT` in the various blocks -/

lemma PolyLoop.wrapT_eq_zero (L : PolyLoop Ω) (a b : I) {k : Fin (L.wrapM a b + 1)}
    (h0 : (k:ℕ) = 0) : L.wrapT a b k = 0 := by
  unfold PolyLoop.wrapT
  rw [dif_pos h0]

lemma PolyLoop.wrapT_eq_blockA (L : PolyLoop Ω) (a b : I) {k : Fin (L.wrapM a b + 1)}
    (h1 : 1 ≤ (k:ℕ)) (h2 : (k:ℕ) ≤ L.wrapNB b) :
    L.wrapT a b k = L.wrapTA b ⟨(L.gidx b : ℕ) + (k:ℕ), by
        have h := L.gidx_add_le b h2
        omega⟩ (by
      refine L.le_t_of_gidx_le b ?_ ?_
      · omega
      · have h := L.gidx_add_le b h2
        omega) := by
  unfold PolyLoop.wrapT
  rw [dif_neg (by omega), dif_pos h2]

lemma PolyLoop.wrapT_eq_mid (L : PolyLoop Ω) (a b : I) {k : Fin (L.wrapM a b + 1)}
    (h2 : (k:ℕ) = L.wrapNB b + 1) :
    L.wrapT a b k = (⟨(1:ℝ)/2, by norm_num⟩ : I) := by
  unfold PolyLoop.wrapT
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos h2]

lemma PolyLoop.wrapT_eq_blockC (L : PolyLoop Ω) (a b : I) {k : Fin (L.wrapM a b + 1)}
    (h2 : L.wrapNB b + 1 < (k:ℕ)) (h3 : (k:ℕ) ≤ L.wrapNB b + 1 + L.wrapNC a) :
    L.wrapT a b k = L.wrapTC a ⟨(k:ℕ) - L.wrapNB b - 1, by
        have h := L.wrapNC_le a
        have h4 : (L.gidx a : ℕ) < L.M := (L.gidx a).2
        omega⟩ (by
      refine L.t_le_a_of_wrapNC a ?_ ?_
      · have h := L.wrapNC_le a
        omega
      · have h := L.wrapNC_le a
        have h4 : (L.gidx a : ℕ) < L.M := (L.gidx a).2
        omega) := by
  unfold PolyLoop.wrapT
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_pos h3]

lemma PolyLoop.wrapT_eq_one (L : PolyLoop Ω) (a b : I) {k : Fin (L.wrapM a b + 1)}
    (h3 : L.wrapNB b + 1 + L.wrapNC a < (k:ℕ)) :
    L.wrapT a b k = 1 := by
  have hdef : L.wrapM a b = 2 + L.wrapNB b + L.wrapNC a := rfl
  unfold PolyLoop.wrapT
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega), dif_neg (by omega)]

/-! #### Bounds for the block values -/

/-- The affine map `x ↦ (1 - x) * b + x * 1` is monotone when `b < 1`. -/
lemma affine_mono_of_lt_one {b : ℝ} (hb : b < 1) :
    Monotone (fun x : ℝ => (1 - x) * b + x * 1) := by
  intro x y hxy
  nlinarith [hb, hxy]

/-- `Icc.convexComb b 1` is monotone in its parameter when `b < 1`. -/
lemma Icc.convexComb_mono_right {b : I} (hb1 : b < 1) :
    Monotone (fun x : I => Icc.convexComb b 1 x) := by
  intro x y hxy
  have h1 : ((Icc.convexComb b 1 x : I) : ℝ) ≤ ((Icc.convexComb b 1 y : I) : ℝ) := by
    rw [Icc.coe_convexComb, Icc.coe_convexComb]
    have hb' : (b:ℝ) < 1 := Subtype.coe_lt_coe.mpr hb1
    have hxy' : (x:ℝ) ≤ (y:ℝ) := Subtype.coe_le_coe.mpr hxy
    have h := affine_mono_of_lt_one hb' hxy'
    simpa using h
  exact Subtype.coe_le_coe.mp h1

/-- Strict version of `affine_mono_of_lt_one`. -/
lemma affine_strictMono_of_lt_one {b : ℝ} (hb : b < 1) :
    StrictMono (fun x : ℝ => (1 - x) * b + x * 1) := by
  intro x y hxy
  nlinarith [hb, hxy]

/-- Strict version of `affine_mono_of_lt_one` for the interval `[0,a]`, `a > 0`. -/
lemma affine_strictMono_of_pos {a : ℝ} (ha : 0 < a) :
    StrictMono (fun x : ℝ => (1 - x) * 0 + x * a) := by
  intro x y hxy
  nlinarith [ha, hxy]

lemma Icc.convexComb_strictMono_right {b : I} (hb1 : b < 1) :
    StrictMono (fun x : I => Icc.convexComb b 1 x) := by
  intro x y hxy
  have h := affine_strictMono_of_lt_one (Subtype.coe_lt_coe.mpr hb1)
    (Subtype.coe_lt_coe.mpr hxy)
  apply Subtype.coe_lt_coe.mp
  rw [Icc.coe_convexComb, Icc.coe_convexComb]
  simpa using h

lemma Icc.convexComb_strictMono_right' {a : I} (ha0 : 0 < a) :
    StrictMono (fun x : I => Icc.convexComb 0 a x) := by
  intro x y hxy
  have h := affine_strictMono_of_pos (Subtype.coe_lt_coe.mpr ha0)
    (Subtype.coe_lt_coe.mpr hxy)
  apply Subtype.coe_lt_coe.mp
  rw [Icc.coe_convexComb, Icc.coe_convexComb]
  simpa using h

/-- The block-A parameters are monotone in the index (needs `b < 1`). -/
lemma PolyLoop.wrapTA_mono (L : PolyLoop Ω) {b : I} (hb1 : b < 1) {m m' : Fin (L.M+1)}
    (hb : b ≤ L.t m) (hb' : b ≤ L.t m') (hm : m ≤ m') :
    L.wrapTA b m hb ≤ L.wrapTA b m' hb' := by
  have h1 : Icc.convexComb b 1 (L.wrapS b m hb) ≤ Icc.convexComb b 1 (L.wrapS b m' hb') := by
    rw [L.wrapS_spec b m hb, L.wrapS_spec b m' hb']
    exact L.htmono hm
  have h2 : L.wrapS b m hb ≤ L.wrapS b m' hb' := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd h1 (not_le.mpr ((Icc.convexComb_strictMono_right hb1) hlt))
  have h2' : (L.wrapS b m hb : ℝ) ≤ (L.wrapS b m' hb' : ℝ) := Subtype.coe_le_coe.mpr h2
  show (((L.wrapS b m hb : I) : ℝ)) / 2 ≤ (((L.wrapS b m' hb' : I) : ℝ)) / 2
  exact div_le_div_of_nonneg_right h2' (by norm_num)

/-- The block-C parameters are monotone in the index (needs `0 < a`). -/
lemma PolyLoop.wrapTC_mono (L : PolyLoop Ω) {a : I} (ha0 : 0 < a) {m m' : Fin (L.M+1)}
    (hm : L.t m ≤ a) (hm' : L.t m' ≤ a) (hmm : m ≤ m') :
    L.wrapTC a m hm ≤ L.wrapTC a m' hm' := by
  have h1 : Icc.convexComb 0 a (L.wrapS0 a m hm) ≤ Icc.convexComb 0 a (L.wrapS0 a m' hm') := by
    rw [L.wrapS0_spec a m hm, L.wrapS0_spec a m' hm']
    exact L.htmono hmm
  have h2 : L.wrapS0 a m hm ≤ L.wrapS0 a m' hm' := by
    by_contra hlt
    rw [not_le] at hlt
    exact absurd h1 (not_le.mpr ((Icc.convexComb_strictMono_right' ha0) hlt))
  have h2' : (L.wrapS0 a m hm : ℝ) ≤ (L.wrapS0 a m' hm' : ℝ) := Subtype.coe_le_coe.mpr h2
  show (1 + ((L.wrapS0 a m hm : I) : ℝ)) / 2 ≤ (1 + ((L.wrapS0 a m' hm' : I) : ℝ)) / 2
  exact div_le_div_of_nonneg_right (by linarith [h2']) (by norm_num)

lemma PolyLoop.zero_le_wrapTA (L : PolyLoop Ω) (b : I) (m : Fin (L.M+1)) (hb : b ≤ L.t m) :
    (⟨(0:ℝ), by norm_num⟩ : I) ≤ L.wrapTA b m hb := by
  show (0:ℝ) ≤ ((L.wrapS b m hb : I) : ℝ) / 2
  have := (L.wrapS b m hb).2.1
  linarith

lemma PolyLoop.wrapTA_le_half (L : PolyLoop Ω) (b : I) (m : Fin (L.M+1)) (hb : b ≤ L.t m) :
    L.wrapTA b m hb ≤ (⟨(1:ℝ)/2, by norm_num⟩ : I) := by
  show ((L.wrapS b m hb : I) : ℝ) / 2 ≤ (1:ℝ)/2
  have := (L.wrapS b m hb).2.2
  linarith

lemma PolyLoop.zero_le_wrapTC (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1)) (hm : L.t m ≤ a) :
    (⟨(0:ℝ), by norm_num⟩ : I) ≤ L.wrapTC a m hm := by
  show (0:ℝ) ≤ (1 + ((L.wrapS0 a m hm : I) : ℝ)) / 2
  have := (L.wrapS0 a m hm).2.1
  linarith

lemma PolyLoop.half_le_wrapTC (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1)) (hm : L.t m ≤ a) :
    (⟨(1:ℝ)/2, by norm_num⟩ : I) ≤ L.wrapTC a m hm := by
  show (1:ℝ)/2 ≤ (1 + ((L.wrapS0 a m hm : I) : ℝ)) / 2
  have := (L.wrapS0 a m hm).2.1
  linarith

lemma PolyLoop.wrapTC_le_one (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1)) (hm : L.t m ≤ a) :
    L.wrapTC a m hm ≤ (⟨(1:ℝ), by norm_num⟩ : I) := by
  show (1 + ((L.wrapS0 a m hm : I) : ℝ)) / 2 ≤ (1:ℝ)
  have := (L.wrapS0 a m hm).2.2
  linarith

lemma PolyLoop.zero_le_wrapT (L : PolyLoop Ω) (a b : I) (k : Fin (L.wrapM a b + 1)) :
    (0:I) ≤ L.wrapT a b k := by
  by_cases h0 : (k:ℕ) = 0
  · rw [L.wrapT_eq_zero a b h0]
  · by_cases h1 : (k:ℕ) ≤ L.wrapNB b
    · rw [L.wrapT_eq_blockA a b (by omega) h1]; exact L.zero_le_wrapTA b _ _
    · by_cases h2 : (k:ℕ) = L.wrapNB b + 1
      · rw [L.wrapT_eq_mid a b h2]
        show (0:ℝ) ≤ (1:ℝ)/2
        norm_num
      · by_cases h3 : (k:ℕ) ≤ L.wrapNB b + 1 + L.wrapNC a
        · rw [L.wrapT_eq_blockC a b (by omega) h3]; exact L.zero_le_wrapTC a _ _
        · rw [L.wrapT_eq_one a b (by omega)]
          show (0:ℝ) ≤ 1
          norm_num

/-- If the block-A range is nonempty then `b < 1`. -/
lemma PolyLoop.lt_one_of_wrapNB_pos (L : PolyLoop Ω) (hstrict : StrictMono L.t) {b : I}
    (h : 0 < L.wrapNB b) : b < 1 := by
  have hnB : L.wrapNB b = L.M - 1 - (L.gidx b : ℕ) := rfl
  have hgb : (L.gidx b : ℕ) < L.M := (L.gidx b).2
  rw [hnB] at h
  have hg : (L.gidx b : ℕ) < L.M - 1 := by omega
  have hlt : (L.gidx b).succ < (Fin.last L.M) := by
    apply Fin.lt_iff_val_lt_val.mpr
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have h1 : L.t (L.gidx b).succ < L.t (Fin.last L.M) := hstrict hlt
  rw [L.ht1] at h1
  exact lt_of_le_of_lt (le_gidx_succ L b) h1

/-- If the block-C range is nonempty then `0 < a`. -/
lemma PolyLoop.lt_zero_of_wrapNC_pos (L : PolyLoop Ω) (hstrict : StrictMono L.t) {a : I}
    (h : 0 < L.wrapNC a) : 0 < a := by
  have hnC : L.wrapNC a = if (L.gidx a : ℕ) = 0 then 0
      else (L.gidx a : ℕ) - 1 + (if a = L.t (L.gidx a).castSucc then 0 else 1) := rfl
  have hg : 0 < (L.gidx a : ℕ) := by
    by_contra hc
    have hc' : (L.gidx a : ℕ) = 0 := by omega
    rw [hnC, if_pos hc'] at h
    omega
  have h1 : (0 : Fin (L.M+1)) < (L.gidx a).castSucc := by
    apply Fin.lt_iff_val_lt_val.mpr
    simp only [Fin.val_castSucc, Fin.val_zero]
    omega
  have h2 : L.t 0 < L.t (L.gidx a).castSucc := hstrict h1
  rw [L.ht0] at h2
  exact lt_of_lt_of_le h2 (gidx_le L a)

lemma PolyLoop.wrapT_succ_le (L : PolyLoop Ω) (hstrict : StrictMono L.t) (a b : I)
    (k : Fin (L.wrapM a b)) : L.wrapT a b k.castSucc ≤ L.wrapT a b k.succ := by
  have hcast : ((k.castSucc : Fin (L.wrapM a b + 1)) : ℕ) = (k:ℕ) := Fin.val_castSucc ..
  have hsucc : ((k.succ : Fin (L.wrapM a b + 1)) : ℕ) = (k:ℕ) + 1 := Fin.val_succ ..
  have hM : L.wrapM a b = 2 + L.wrapNB b + L.wrapNC a := rfl
  rcases Nat.eq_zero_or_pos (k:ℕ) with hk0 | hkpos
  · rw [L.wrapT_eq_zero a b (k := k.castSucc) (by rw [hcast, hk0])]
    exact L.zero_le_wrapT a b k.succ
  · by_cases hA : (k:ℕ) ≤ L.wrapNB b
    · rw [L.wrapT_eq_blockA a b (k := k.castSucc) (by rw [hcast]; omega) (by rw [hcast]; exact hA)]
      by_cases hA' : (k:ℕ) + 1 ≤ L.wrapNB b
      · rw [L.wrapT_eq_blockA a b (k := k.succ) (by rw [hsucc]; omega) (by rw [hsucc]; omega)]
        refine L.wrapTA_mono (L.lt_one_of_wrapNB_pos hstrict (by omega)) _ _ ?_
        exact Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_mk, hsucc, hcast]; omega)
      · have h2 : (k:ℕ) + 1 = L.wrapNB b + 1 := by omega
        rw [L.wrapT_eq_mid a b (k := k.succ) (by rw [hsucc]; exact h2)]
        exact L.wrapTA_le_half b _ _
    · by_cases hmid : (k:ℕ) = L.wrapNB b + 1
      · rw [L.wrapT_eq_mid a b (k := k.castSucc) (by rw [hcast]; exact hmid)]
        by_cases hC : (k:ℕ) + 1 ≤ L.wrapNB b + 1 + L.wrapNC a
        · rw [L.wrapT_eq_blockC a b (k := k.succ) (by rw [hsucc]; omega) (by rw [hsucc]; omega)]
          exact L.half_le_wrapTC a _ _
        · have h1 : (k:ℕ) + 1 = L.wrapM a b := by omega
          rw [L.wrapT_eq_one a b (k := k.succ) (by rw [hsucc, h1, hM]; omega)]
          show (1:ℝ)/2 ≤ (1:ℝ)
          norm_num
      · by_cases hC : (k:ℕ) ≤ L.wrapNB b + 1 + L.wrapNC a
        · have ha0 : 0 < a := L.lt_zero_of_wrapNC_pos hstrict (by omega)
          rw [L.wrapT_eq_blockC a b (k := k.castSucc) (by rw [hcast]; omega)
            (by rw [hcast]; exact hC)]
          by_cases hC' : (k:ℕ) + 1 ≤ L.wrapNB b + 1 + L.wrapNC a
          · rw [L.wrapT_eq_blockC a b (k := k.succ) (by rw [hsucc]; omega) (by rw [hsucc]; omega)]
            refine L.wrapTC_mono ha0 _ _ ?_
            exact Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_mk, hsucc, hcast]; omega)
          · have h1 : (k:ℕ) + 1 = L.wrapM a b := by omega
            rw [L.wrapT_eq_one a b (k := k.succ) (by rw [hsucc, h1, hM]; omega)]
            exact L.wrapTC_le_one a _ _
        · exfalso
          omega

lemma PolyLoop.wrapT_mono (L : PolyLoop Ω) (hstrict : StrictMono L.t) (a b : I) :
    Monotone (L.wrapT a b) :=
  Fin.monotone_iff_le_succ.mpr (L.wrapT_succ_le hstrict a b)

/-! #### The two halves of the wrapping loop -/

/-- Doubling a parameter that is at most `1/2` (used for the first half of the wrap). -/
def dblI (x : I) (hx : (x:ℝ) ≤ 1/2) : I :=
  ⟨2 * (x:ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨x.2.1, hx⟩⟩

/-- Doubling and shifting a parameter that is at least `1/2` (second half of the wrap). -/
def dblI' (x : I) (hx : 1/2 ≤ (x:ℝ)) : I :=
  ⟨2 * (x:ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2 ⟨hx, x.2.2⟩⟩

@[simp] lemma dblI_val (x : I) (hx : (x:ℝ) ≤ 1/2) : ((dblI x hx : I) : ℝ) = 2 * (x:ℝ) := rfl

@[simp] lemma dblI'_val (x : I) (hx : 1/2 ≤ (x:ℝ)) : ((dblI' x hx : I) : ℝ) = 2 * (x:ℝ) - 1 := rfl

lemma PolyLoop.wrapLoop_first (L : PolyLoop Ω) {a b : I} (hval : L.loop a = L.loop b)
    {s : I} (hs : (s:ℝ) ≤ 1/2) :
    ((L.wrapLoop a b hval s : ↥Ω) : ℂ) =
      ((L.loop (Icc.convexComb b 1 (dblI s hs)) : ↥Ω) : ℂ) := by
  rw [PolyLoop.wrapLoop, Path.trans_apply, dif_pos hs, Path.cast_coe]
  rfl

lemma PolyLoop.wrapLoop_half (L : PolyLoop Ω) {a b : I} (hval : L.loop a = L.loop b)
    {s : I} (hs : 1/2 ≤ (s:ℝ)) :
    ((L.wrapLoop a b hval s : ↥Ω) : ℂ) =
      ((L.loop (Icc.convexComb 0 a (dblI' s hs)) : ↥Ω) : ℂ) := by
  rw [PolyLoop.wrapLoop, Path.trans_apply]
  rcases lt_or_ge ((1:ℝ)/2) ((s:ℝ)) with h | h
  · rw [dif_neg (by linarith), Path.cast_coe]
    rfl
  · rw [dif_pos h, Path.cast_coe]
    show ((L.loop (Icc.convexComb b 1 (⟨2 * (s:ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
        ⟨s.2.1, h⟩⟩ : I)) : ↥Ω) : ℂ) = ((L.loop (Icc.convexComb 0 a (dblI' s hs)) : ↥Ω) : ℂ)
    have h2s : (⟨2 * (s:ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨s.2.1, h⟩⟩ : I) = 1 := by
      apply Subtype.ext
      show 2 * (s:ℝ) = (1:ℝ)
      linarith
    have h2s1 : ((dblI' s hs : I) : ℝ) = (0:ℝ) := by
      rw [dblI'_val]
      linarith
    rw [h2s, Icc.convexComb_one]
    show ((L.loop (1:I) : ↥Ω) : ℂ) = ((L.loop (Icc.convexComb 0 a (dblI' s hs)) : ↥Ω) : ℂ)
    rw [show dblI' s hs = (0:I) from Subtype.ext h2s1,
      Icc.convexComb_zero]
    exact congrArg (fun z : ↥Ω => (z:ℂ)) (L.loop.target'.trans L.loop.source'.symm)

lemma PolyLoop.two_mul_wrapTA (L : PolyLoop Ω) (b : I) (m : Fin (L.M+1)) (hb : b ≤ L.t m)
    (hle : ((L.wrapTA b m hb : I) : ℝ) ≤ 1/2) :
    (⟨2 * ((L.wrapTA b m hb : I) : ℝ), (unitInterval.mul_pos_mem_iff zero_lt_two).2
      ⟨(L.wrapTA b m hb).2.1, hle⟩⟩ : I) = L.wrapS b m hb := by
  apply Subtype.ext
  show 2 * (((L.wrapS b m hb : I) : ℝ) / 2) = ((L.wrapS b m hb : I) : ℝ)
  ring

lemma PolyLoop.two_mul_wrapTC (L : PolyLoop Ω) (a : I) (m : Fin (L.M+1)) (hm : L.t m ≤ a)
    (hle : 1/2 ≤ ((L.wrapTC a m hm : I) : ℝ)) :
    (⟨2 * ((L.wrapTC a m hm : I) : ℝ) - 1, unitInterval.two_mul_sub_one_mem_iff.2
      ⟨hle, (L.wrapTC a m hm).2.2⟩⟩ : I) = L.wrapS0 a m hm := by
  apply Subtype.ext
  show 2 * ((1 + ((L.wrapS0 a m hm : I) : ℝ)) / 2) - 1 = ((L.wrapS0 a m hm : I) : ℝ)
  ring

/-- Affineness transported through an affine reparametrisation of the parameter. -/
lemma PolyLoop.haff_transport (L : PolyLoop Ω) {P Q c d α β : I}
    (hG : ∀ u, ((L.loop (Icc.convexComb α β u) : ↥Ω) : ℂ)
      = (1 - (u:ℝ)) * ((L.loop α : ↥Ω) : ℂ) + (u:ℝ) * ((L.loop β : ↥Ω) : ℂ))
    (hc : Icc.convexComb P Q c = α) (hd : Icc.convexComb P Q d = β) (x : I) :
    ((L.loop (Icc.convexComb P Q (Icc.convexComb c d x)) : ↥Ω) : ℂ)
      = (1 - (x:ℝ)) * ((L.loop (Icc.convexComb P Q c) : ↥Ω) : ℂ)
        + (x:ℝ) * ((L.loop (Icc.convexComb P Q d) : ↥Ω) : ℂ) := by
  rw [← Icc.convexComb_convexComb P Q c d x, hc, hd]
  exact hG x

lemma PolyLoop.haff_transport' (L : PolyLoop Ω) {P Q c d : I} {p : Fin L.M}
    (hc : Icc.convexComb P Q c = P) (hd : Icc.convexComb P Q d = L.t p.succ)
    (hP : L.t p.castSucc ≤ P) (hPβ : P ≤ L.t p.succ) (x : I) :
    ((L.loop (Icc.convexComb P Q (Icc.convexComb c d x)) : ↥Ω) : ℂ)
      = (1 - (x:ℝ)) * ((L.loop (Icc.convexComb P Q c) : ↥Ω) : ℂ)
        + (x:ℝ) * ((L.loop (Icc.convexComb P Q d) : ↥Ω) : ℂ) :=
  L.haff_transport (affine_subinterval (G := fun u => ((L.loop u : ↥Ω) : ℂ)) (L.haff p)
    hP hPβ (le_refl _)) hc hd x

lemma PolyLoop.haff_transport'' (L : PolyLoop Ω) {P Q c d : I} {p : Fin L.M}
    (hc : Icc.convexComb P Q c = L.t p.castSucc) (hd : Icc.convexComb P Q d = Q)
    (hQ0 : L.t p.castSucc ≤ Q) (hQ : Q ≤ L.t p.succ) (x : I) :
    ((L.loop (Icc.convexComb P Q (Icc.convexComb c d x)) : ↥Ω) : ℂ)
      = (1 - (x:ℝ)) * ((L.loop (Icc.convexComb P Q c) : ↥Ω) : ℂ)
        + (x:ℝ) * ((L.loop (Icc.convexComb P Q d) : ↥Ω) : ℂ) :=
  L.haff_transport (affine_subinterval (G := fun u => ((L.loop u : ↥Ω) : ℂ)) (L.haff p)
    (le_refl _) hQ0 hQ) hc hd x
lemma PolyLoop.le_t_one_of_wrapNC_eq_zero (L : PolyLoop Ω) {a : I} (h : L.wrapNC a = 0) :
    a ≤ L.t (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1)) := by
  have hnC : L.wrapNC a = if (L.gidx a : ℕ) = 0 then 0
      else (L.gidx a : ℕ) - 1 + (if a = L.t (L.gidx a).castSucc then 0 else 1) := rfl
  rw [hnC] at h
  by_cases hi : (L.gidx a : ℕ) = 0
  · have h1 : a ≤ L.t (L.gidx a).succ := le_gidx_succ L a
    have he : (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1)) = (L.gidx a).succ := by
      apply Fin.ext
      rw [Fin.val_succ]
      simp only [Fin.val_mk]
      omega
    rwa [he]
  · rw [if_neg hi] at h
    by_cases hai : a = L.t (L.gidx a).castSucc
    · rw [if_pos hai] at h
      have he : (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1)) = (L.gidx a).castSucc := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_mk]
        omega
      rw [he]
      exact le_of_eq hai
    · rw [if_neg hai] at h
      omega

lemma PolyLoop.le_t_wrapNC_succ (L : PolyLoop Ω) (a : I) :
    a ≤ L.t (⟨L.wrapNC a + 1, by
      have h := L.wrapNC_le a
      have h2 := (L.gidx a).2
      omega⟩ : Fin (L.M+1)) := by
  have hnC : L.wrapNC a = if (L.gidx a : ℕ) = 0 then 0
      else (L.gidx a : ℕ) - 1 + (if a = L.t (L.gidx a).castSucc then 0 else 1) := rfl
  by_cases hi : (L.gidx a : ℕ) = 0
  · have he : (⟨L.wrapNC a + 1, by
        have h := L.wrapNC_le a
        have h2 := (L.gidx a).2
        omega⟩ : Fin (L.M+1)) = (L.gidx a).succ := by
      apply Fin.ext
      show L.wrapNC a + 1 = (L.gidx a : ℕ) + 1
      rw [hnC, if_pos hi]
      omega
    rw [he]
    exact le_gidx_succ L a
  · have hg1 : 1 ≤ (L.gidx a : ℕ) := by omega
    by_cases hai : a = L.t (L.gidx a).castSucc
    · have he : (⟨L.wrapNC a + 1, by
          have h := L.wrapNC_le a
          have h2 := (L.gidx a).2
          omega⟩ : Fin (L.M+1)) = (L.gidx a).castSucc := by
        apply Fin.ext
        show L.wrapNC a + 1 = (L.gidx a : ℕ)
        rw [hnC, if_neg hi, if_pos hai]
        omega
      rw [he]
      exact le_of_eq hai
    · have he : (⟨L.wrapNC a + 1, by
          have h := L.wrapNC_le a
          have h2 := (L.gidx a).2
          omega⟩ : Fin (L.M+1)) = (L.gidx a).succ := by
        apply Fin.ext
        show L.wrapNC a + 1 = (L.gidx a : ℕ) + 1
        rw [hnC, if_neg hi, if_neg hai]
        omega
      rw [he]
      exact le_gidx_succ L a

lemma PolyLoop.wrapT_affine (L : PolyLoop Ω) {a b : I} (hval : L.loop a = L.loop b)
    (k : Fin (L.wrapM a b)) (u : I) :
    ((L.wrapLoop a b hval (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) : ↥Ω) : ℂ)
      = (1 - (u:ℝ)) * ((L.wrapLoop a b hval (L.wrapT a b k.castSucc) : ↥Ω) : ℂ)
        + (u:ℝ) * ((L.wrapLoop a b hval (L.wrapT a b k.succ) : ↥Ω) : ℂ) := by
  have hcast : ((k.castSucc : Fin (L.wrapM a b + 1)) : ℕ) = (k:ℕ) := Fin.val_castSucc ..
  have hsucc : ((k.succ : Fin (L.wrapM a b + 1)) : ℕ) = (k:ℕ) + 1 := Fin.val_succ ..
  have hM : L.wrapM a b = 2 + L.wrapNB b + L.wrapNC a := rfl
  have hnB : L.wrapNB b = L.M - 1 - (L.gidx b : ℕ) := rfl
  have hjnB : (L.gidx b : ℕ) + L.wrapNB b = L.M - 1 := by rw [hnB]; omega
  rcases Nat.eq_zero_or_pos (k:ℕ) with hk0 | hkpos
  · -- ### first interval of the first half (kk = 0)
    have hω : L.wrapT a b k.castSucc = 0 := L.wrapT_eq_zero a b (by rw [hcast, hk0])
    have hcle : ((L.wrapT a b k.castSucc : I) : ℝ) ≤ 1/2 := by rw [hω]; norm_num
    by_cases h1 : 1 ≤ L.wrapNB b
    · set m : Fin (L.M+1) := ⟨(L.gidx b : ℕ) + ((k.succ : Fin (L.wrapM a b + 1)) : ℕ), by
          have h := L.gidx_add_le b (k := 1) (by omega)
          omega⟩ with hm
      have hmle : b ≤ L.t m := by
        refine L.le_t_of_gidx_le b ?_ ?_
        · omega
        · have h := L.gidx_add_le b (k := 1) (by omega)
          omega
      have hω' : L.wrapT a b k.succ = L.wrapTA b m hmle :=
        L.wrapT_eq_blockA a b (k := k.succ) (by rw [hsucc]; omega) (by rw [hsucc]; omega)
      have hsub : ((L.wrapT a b k.succ : I) : ℝ) ≤ 1/2 := by
        rw [hω']; exact L.wrapTA_le_half b m hmle
      have hs : ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) ≤ 1/2 := by
        rw [Icc.coe_convexComb]
        nlinarith [u.2.1, u.2.2, hcle, hsub]
      rw [L.wrapLoop_first hval hs, L.wrapLoop_first hval hcle, L.wrapLoop_first hval hsub]
      have harg : dblI (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
          = Icc.convexComb (dblI (L.wrapT a b k.castSucc) hcle) (dblI (L.wrapT a b k.succ) hsub) u := by
        apply Subtype.ext
        simp only [Icc.coe_convexComb, dblI_val]
        ring
      rw [harg]
      refine L.haff_transport' (p := L.gidx b) ?_ ?_ ?_ ?_ u
      · rw [show dblI (L.wrapT a b k.castSucc) hcle = 0 from by
            apply Subtype.ext
            rw [dblI_val, hω]; norm_num,
          Icc.convexComb_zero]
      · rw [show dblI (L.wrapT a b k.succ) hsub = L.wrapS b m hmle from by
            apply Subtype.ext
            rw [dblI_val, hω']
            show 2 * (((L.wrapS b m hmle : I) : ℝ) / 2) = ((L.wrapS b m hmle : I) : ℝ)
            ring,
          L.wrapS_spec b m hmle]
        exact congrArg L.t (Fin.ext (by
          rw [hm]
          simp only [Fin.val_mk, Fin.val_succ]
          omega))
      · exact gidx_le L b
      · exact le_gidx_succ L b
    · -- the second breakpoint is the junction
      have hω' : L.wrapT a b k.succ = (⟨(1:ℝ)/2, by norm_num⟩ : I) := by
        refine L.wrapT_eq_mid a b (k := k.succ) ?_
        rw [hsucc]; omega
      have hsub : ((L.wrapT a b k.succ : I) : ℝ) ≤ 1/2 := by
        rw [hω']
      have hs : ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) ≤ 1/2 := by
        rw [Icc.coe_convexComb]
        nlinarith [u.2.1, u.2.2, hcle, hsub]
      rw [L.wrapLoop_first hval hs, L.wrapLoop_first hval hcle, L.wrapLoop_first hval hsub]
      have harg : dblI (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
          = Icc.convexComb (dblI (L.wrapT a b k.castSucc) hcle) (dblI (L.wrapT a b k.succ) hsub) u := by
        apply Subtype.ext
        simp only [Icc.coe_convexComb, dblI_val]
        ring
      rw [harg]
      refine L.haff_transport' (p := L.gidx b) ?_ ?_ ?_ ?_ u
      · rw [show dblI (L.wrapT a b k.castSucc) hcle = 0 from by
            apply Subtype.ext
            rw [dblI_val, hω]; norm_num,
          Icc.convexComb_zero]
      · rw [show dblI (L.wrapT a b k.succ) hsub = 1 from by
            apply Subtype.ext
            rw [dblI_val, hω']
            norm_num,
          Icc.convexComb_one,
          show (L.gidx b).succ = Fin.last L.M from Fin.ext (by
            rw [Fin.val_succ, Fin.val_last]; rw [hnB] at h1; omega),
          L.ht1]
      · exact gidx_le L b
      · exact le_gidx_succ L b
  · -- kk ≥ 1
    by_cases hA : (k:ℕ) ≤ L.wrapNB b
    · -- ### block A of the first half
      set m : Fin (L.M+1) := ⟨(L.gidx b : ℕ) + (k:ℕ), by
          have h := L.gidx_add_le b hA
          omega⟩ with hm
      have hmv : (m:ℕ) = (L.gidx b : ℕ) + (k:ℕ) := rfl
      set p : Fin L.M := ⟨(L.gidx b : ℕ) + (k:ℕ), by
          have h := L.gidx_add_le b hA
          omega⟩ with hp
      have hpv : (p:ℕ) = (L.gidx b : ℕ) + (k:ℕ) := rfl
      have hpc : (p.castSucc : Fin (L.M+1)) = m := by
        apply Fin.ext
        show (L.gidx b : ℕ) + (k:ℕ) = (L.gidx b : ℕ) + (k:ℕ)
        rfl
      have hmle : b ≤ L.t m := by
        refine L.le_t_of_gidx_le b ?_ ?_
        · omega
        · have h := L.gidx_add_le b hA; omega
      have hω : L.wrapT a b k.castSucc = L.wrapTA b m hmle :=
        L.wrapT_eq_blockA a b (k := k.castSucc) (by rw [hcast]; omega) (by rw [hcast]; exact hA)
      have hcle : ((L.wrapT a b k.castSucc : I) : ℝ) ≤ 1/2 := by
        rw [hω]; exact L.wrapTA_le_half b m hmle
      by_cases hA' : (k:ℕ) + 1 ≤ L.wrapNB b
      · -- both endpoints in block A
        set m' : Fin (L.M+1) := ⟨(L.gidx b : ℕ) + ((k.succ : Fin (L.wrapM a b + 1)) : ℕ), by
            have h := L.gidx_add_le b hA'
            omega⟩ with hm'
        have hm'le : b ≤ L.t m' := by
          refine L.le_t_of_gidx_le b ?_ ?_
          · omega
          · have h := L.gidx_add_le b hA'; omega
        have hω' : L.wrapT a b k.succ = L.wrapTA b m' hm'le :=
          L.wrapT_eq_blockA a b (k := k.succ) (by rw [hsucc]; omega) (by rw [hsucc]; omega)
        have hsub : ((L.wrapT a b k.succ : I) : ℝ) ≤ 1/2 := by
          rw [hω']; exact L.wrapTA_le_half b m' hm'le
        have hs : ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) ≤ 1/2 := by
          rw [Icc.coe_convexComb]
          nlinarith [u.2.1, u.2.2, hcle, hsub]
        rw [L.wrapLoop_first hval hs, L.wrapLoop_first hval hcle, L.wrapLoop_first hval hsub]
        have harg : dblI (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
            = Icc.convexComb (dblI (L.wrapT a b k.castSucc) hcle) (dblI (L.wrapT a b k.succ) hsub) u := by
          apply Subtype.ext
          simp only [Icc.coe_convexComb, dblI_val]
          ring
        rw [harg]
        refine L.haff_transport (P := b) (Q := 1) (L.haff p) ?_ ?_ u
        · rw [show dblI (L.wrapT a b k.castSucc) hcle = L.wrapS b m hmle from by
              apply Subtype.ext
              rw [dblI_val, hω]
              show 2 * (((L.wrapS b m hmle : I) : ℝ) / 2) = ((L.wrapS b m hmle : I) : ℝ)
              ring,
            L.wrapS_spec b m hmle]
          rw [hpc]
        · rw [show dblI (L.wrapT a b k.succ) hsub = L.wrapS b m' hm'le from by
              apply Subtype.ext
              rw [dblI_val, hω']
              show 2 * (((L.wrapS b m' hm'le : I) : ℝ) / 2) = ((L.wrapS b m' hm'le : I) : ℝ)
              ring,
            L.wrapS_spec b m' hm'le]
          exact congrArg L.t (Fin.ext (by
            show (L.gidx b : ℕ) + ((k.succ : Fin (L.wrapM a b + 1)) : ℕ)
              = (L.gidx b : ℕ) + (k:ℕ) + 1
            rw [hsucc]
            omega))
      · -- kk = nB : the second endpoint is the junction
        have hω' : L.wrapT a b k.succ = (⟨(1:ℝ)/2, by norm_num⟩ : I) := by
          refine L.wrapT_eq_mid a b (k := k.succ) ?_
          omega
        have hsub : ((L.wrapT a b k.succ : I) : ℝ) ≤ 1/2 := by
          rw [hω']
        have hs : ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) ≤ 1/2 := by
          rw [Icc.coe_convexComb]
          nlinarith [u.2.1, u.2.2, hcle, hsub]
        rw [L.wrapLoop_first hval hs, L.wrapLoop_first hval hcle, L.wrapLoop_first hval hsub]
        have harg : dblI (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
            = Icc.convexComb (dblI (L.wrapT a b k.castSucc) hcle) (dblI (L.wrapT a b k.succ) hsub) u := by
          apply Subtype.ext
          simp only [Icc.coe_convexComb, dblI_val]
          ring
        rw [harg]
        have hkk : (k:ℕ) = L.wrapNB b := by omega
        refine L.haff_transport (P := b) (Q := 1) (L.haff p) ?_ ?_ u
        · rw [show dblI (L.wrapT a b k.castSucc) hcle = L.wrapS b m hmle from by
              apply Subtype.ext
              rw [dblI_val, hω]
              show 2 * (((L.wrapS b m hmle : I) : ℝ) / 2) = ((L.wrapS b m hmle : I) : ℝ)
              ring,
            L.wrapS_spec b m hmle]
          rw [hpc]
        · have hps : (p.succ : Fin (L.M+1)) = Fin.last L.M := by
            apply Fin.ext
            show (L.gidx b : ℕ) + (k:ℕ) + 1 = L.M
            omega
          rw [show dblI (L.wrapT a b k.succ) hsub = 1 from by
              apply Subtype.ext
              rw [dblI_val, hω']
              norm_num,
            Icc.convexComb_one, hps, L.ht1]
    · by_cases hmid : (k:ℕ) = L.wrapNB b + 1
      · -- ### kk = nB+1 : the first endpoint is the junction
        have hω : L.wrapT a b k.castSucc = (⟨(1:ℝ)/2, by norm_num⟩ : I) := by
          refine L.wrapT_eq_mid a b (k := k.castSucc) ?_
          rw [hcast]; omega
        have hchalf : 1/2 ≤ ((L.wrapT a b k.castSucc : I) : ℝ) := by rw [hω]
        by_cases hC : 1 ≤ L.wrapNC a
        · -- the second endpoint is a block-C breakpoint
          set m'' : Fin (L.M+1) := ⟨((k.succ : Fin (L.wrapM a b + 1)) : ℕ) - L.wrapNB b - 1, by
              have h := L.wrapNC_le a
              have h2 := (L.gidx a).2
              omega⟩ with hm''
          have hm''v : ((k.succ : Fin (L.wrapM a b + 1)) : ℕ) - L.wrapNB b - 1 = 1 := by omega
          have hm''le : L.t m'' ≤ a := by
            refine L.t_le_a_of_wrapNC a ?_ ?_
            · rw [hm''v]; exact hC
            · have h := L.wrapNC_le a; have h2 := (L.gidx a).2; omega
          have hω' : L.wrapT a b k.succ = L.wrapTC a m'' hm''le :=
            L.wrapT_eq_blockC a b (k := k.succ) (by omega) (by omega)
          have hω'half : 1/2 ≤ ((L.wrapT a b k.succ : I) : ℝ) := by
            rw [hω']; exact L.half_le_wrapTC a m'' hm''le
          have hs : 1/2 ≤ ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) := by
            rw [Icc.coe_convexComb]
            nlinarith [u.2.1, u.2.2, hchalf, hω'half]
          rw [L.wrapLoop_half hval hs, L.wrapLoop_half hval hchalf, L.wrapLoop_half hval hω'half]
          have harg : dblI' (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
              = Icc.convexComb (dblI' (L.wrapT a b k.castSucc) hchalf)
                  (dblI' (L.wrapT a b k.succ) hω'half) u := by
            apply Subtype.ext
            simp only [Icc.coe_convexComb, dblI'_val]
            ring
          rw [harg]
          refine L.haff_transport (P := 0) (Q := a)
            (L.haff (⟨0, L.hM⟩ : Fin L.M)) ?_ ?_ u
          · rw [show dblI' (L.wrapT a b k.castSucc) hchalf = 0 from by
                apply Subtype.ext
                rw [dblI'_val, hω]
                norm_num,
              Icc.convexComb_zero,
              show ((⟨0, L.hM⟩ : Fin L.M).castSucc : Fin (L.M+1)) = 0 from by
                apply Fin.ext
                show (0:ℕ) = 0
                rfl,
              L.ht0]
          · rw [show dblI' (L.wrapT a b k.succ) hω'half = L.wrapS0 a m'' hm''le from by
                apply Subtype.ext
                rw [dblI'_val, hω']
                show 2 * ((1 + ((L.wrapS0 a m'' hm''le : I) : ℝ)) / 2) - 1
                  = ((L.wrapS0 a m'' hm''le : I) : ℝ)
                ring,
              L.wrapS0_spec a m'' hm''le]
            exact congrArg L.t (Fin.ext (by
              show ((k.succ : Fin (L.wrapM a b + 1)) : ℕ) - L.wrapNB b - 1 = (0:ℕ) + 1
              omega))
        · -- nC = 0 : the second endpoint is the end of the loop
          have hω' : L.wrapT a b k.succ = (⟨(1:ℝ), by norm_num⟩ : I) := by
            refine L.wrapT_eq_one a b (k := k.succ) ?_
            omega
          have hω'half : 1/2 ≤ ((L.wrapT a b k.succ : I) : ℝ) := by
            rw [hω']; norm_num
          have hs : 1/2 ≤ ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) := by
            rw [Icc.coe_convexComb]
            nlinarith [u.2.1, u.2.2, hchalf, hω'half]
          rw [L.wrapLoop_half hval hs, L.wrapLoop_half hval hchalf, L.wrapLoop_half hval hω'half]
          have harg : dblI' (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
              = Icc.convexComb (dblI' (L.wrapT a b k.castSucc) hchalf)
                  (dblI' (L.wrapT a b k.succ) hω'half) u := by
            apply Subtype.ext
            simp only [Icc.coe_convexComb, dblI'_val]
            ring
          rw [harg]
          refine L.haff_transport'' (p := (⟨0, L.hM⟩ : Fin L.M)) ?_ ?_ ?_ ?_ u
          · rw [show dblI' (L.wrapT a b k.castSucc) hchalf = 0 from by
                apply Subtype.ext
                rw [dblI'_val, hω]
                norm_num,
              Icc.convexComb_zero,
              show ((⟨0, L.hM⟩ : Fin L.M).castSucc : Fin (L.M+1)) = 0 from by
                apply Fin.ext
                show (0:ℕ) = 0
                rfl,
              L.ht0]
          · rw [show dblI' (L.wrapT a b k.succ) hω'half = 1 from by
                apply Subtype.ext
                rw [dblI'_val, hω']
                norm_num,
              Icc.convexComb_one]
          · rw [show ((⟨0, L.hM⟩ : Fin L.M).castSucc : Fin (L.M+1)) = 0 from by
                apply Fin.ext
                show (0:ℕ) = 0
                rfl,
              L.ht0]
            exact a.2.1
          · have hnc0 : L.wrapNC a = 0 := by omega
            have h1 := L.le_t_one_of_wrapNC_eq_zero hnc0
            have hps : ((⟨0, L.hM⟩ : Fin L.M).succ : Fin (L.M+1))
                = (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1)) := by
              apply Fin.ext
              show (0:ℕ) + 1 = 1
              rfl
            rw [hps]
            exact h1
      · -- ### kk ≥ nB+2 : the first endpoint is a block-C breakpoint
        set m'' : Fin (L.M+1) := ⟨(k:ℕ) - L.wrapNB b - 1, by
            have h := L.wrapNC_le a
            have h2 := (L.gidx a).2
            omega⟩ with hm''
        have hm''le : L.t m'' ≤ a := by
          refine L.t_le_a_of_wrapNC a ?_ ?_
          · have h := L.wrapNC_le a
            omega
          · have h := L.wrapNC_le a
            have h2 := (L.gidx a).2
            omega
        have hω : L.wrapT a b k.castSucc = L.wrapTC a m'' hm''le :=
          L.wrapT_eq_blockC a b (k := k.castSucc) (by omega) (by omega)
        have hchalf : 1/2 ≤ ((L.wrapT a b k.castSucc : I) : ℝ) := by
          rw [hω]; exact L.half_le_wrapTC a m'' hm''le
        set p : Fin L.M := ⟨(k:ℕ) - L.wrapNB b - 1, by
            have h := L.wrapNC_le a
            have h2 := (L.gidx a).2
            omega⟩ with hp
        have hpcv : (p.castSucc : Fin (L.M+1)) = m'' := by
          apply Fin.ext
          show (k:ℕ) - L.wrapNB b - 1 = (k:ℕ) - L.wrapNB b - 1
          rfl
        by_cases hC' : (k:ℕ) + 1 ≤ L.wrapNB b + 1 + L.wrapNC a
        · -- both endpoints are block-C breakpoints
          set m''' : Fin (L.M+1) := ⟨((k.succ : Fin (L.wrapM a b + 1)) : ℕ) - L.wrapNB b - 1, by
              have h := L.wrapNC_le a
              have h2 := (L.gidx a).2
              omega⟩ with hm'''
          have hm'''v : ((k.succ : Fin (L.wrapM a b + 1)) : ℕ) - L.wrapNB b - 1
              = ((k:ℕ) - L.wrapNB b - 1) + 1 := by omega
          have hm'''le : L.t m''' ≤ a := by
            refine L.t_le_a_of_wrapNC a ?_ ?_
            · rw [hm'''v]
              have h := L.wrapNC_le a
              omega
            · have h := L.wrapNC_le a
              have h2 := (L.gidx a).2
              omega
          have hω' : L.wrapT a b k.succ = L.wrapTC a m''' hm'''le :=
            L.wrapT_eq_blockC a b (k := k.succ) (by omega) (by omega)
          have hω'half : 1/2 ≤ ((L.wrapT a b k.succ : I) : ℝ) := by
            rw [hω']; exact L.half_le_wrapTC a m''' hm'''le
          have hs : 1/2 ≤ ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) := by
            rw [Icc.coe_convexComb]
            nlinarith [u.2.1, u.2.2, hchalf, hω'half]
          rw [L.wrapLoop_half hval hs, L.wrapLoop_half hval hchalf, L.wrapLoop_half hval hω'half]
          have harg : dblI' (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
              = Icc.convexComb (dblI' (L.wrapT a b k.castSucc) hchalf)
                  (dblI' (L.wrapT a b k.succ) hω'half) u := by
            apply Subtype.ext
            simp only [Icc.coe_convexComb, dblI'_val]
            ring
          rw [harg]
          refine L.haff_transport (P := 0) (Q := a) (L.haff p) ?_ ?_ u
          · rw [show dblI' (L.wrapT a b k.castSucc) hchalf = L.wrapS0 a m'' hm''le from by
                apply Subtype.ext
                rw [dblI'_val, hω]
                show 2 * ((1 + ((L.wrapS0 a m'' hm''le : I) : ℝ)) / 2) - 1
                  = ((L.wrapS0 a m'' hm''le : I) : ℝ)
                ring,
              L.wrapS0_spec a m'' hm''le, hpcv]
          · rw [show dblI' (L.wrapT a b k.succ) hω'half = L.wrapS0 a m''' hm'''le from by
                apply Subtype.ext
                rw [dblI'_val, hω']
                show 2 * ((1 + ((L.wrapS0 a m''' hm'''le : I) : ℝ)) / 2) - 1
                  = ((L.wrapS0 a m''' hm'''le : I) : ℝ)
                ring,
              L.wrapS0_spec a m''' hm'''le]
            exact congrArg L.t (Fin.ext (by
              show ((k.succ : Fin (L.wrapM a b + 1)) : ℕ) - L.wrapNB b - 1
                = ((k:ℕ) - L.wrapNB b - 1) + 1
              omega))
        · -- kk = nB+1+nC : the second endpoint is the end of the loop
          have hω' : L.wrapT a b k.succ = (⟨(1:ℝ), by norm_num⟩ : I) := by
            refine L.wrapT_eq_one a b (k := k.succ) ?_
            omega
          have hω'half : 1/2 ≤ ((L.wrapT a b k.succ : I) : ℝ) := by
            rw [hω']; norm_num
          have hs : 1/2 ≤ ((Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u : I) : ℝ) := by
            rw [Icc.coe_convexComb]
            nlinarith [u.2.1, u.2.2, hchalf, hω'half]
          rw [L.wrapLoop_half hval hs, L.wrapLoop_half hval hchalf, L.wrapLoop_half hval hω'half]
          have harg : dblI' (Icc.convexComb (L.wrapT a b k.castSucc) (L.wrapT a b k.succ) u) hs
              = Icc.convexComb (dblI' (L.wrapT a b k.castSucc) hchalf)
                  (dblI' (L.wrapT a b k.succ) hω'half) u := by
            apply Subtype.ext
            simp only [Icc.coe_convexComb, dblI'_val]
            ring
          rw [harg]
          refine L.haff_transport'' (p := p) ?_ ?_ ?_ ?_ u
          · rw [show dblI' (L.wrapT a b k.castSucc) hchalf = L.wrapS0 a m'' hm''le from by
                apply Subtype.ext
                rw [dblI'_val, hω]
                show 2 * ((1 + ((L.wrapS0 a m'' hm''le : I) : ℝ)) / 2) - 1
                  = ((L.wrapS0 a m'' hm''le : I) : ℝ)
                ring,
              L.wrapS0_spec a m'' hm''le, hpcv]
          · rw [show dblI' (L.wrapT a b k.succ) hω'half = 1 from by
                apply Subtype.ext
                rw [dblI'_val, hω']
                norm_num,
              Icc.convexComb_one]
          · exact hm''le
          · have hkk : (k:ℕ) = L.wrapNB b + 1 + L.wrapNC a := by omega
            have hQ := L.le_t_wrapNC_succ a
            have hps : (p.succ : Fin (L.M+1))
                = (⟨L.wrapNC a + 1, by
                    have h := L.wrapNC_le a
                    have h2 := (L.gidx a).2
                    omega⟩ : Fin (L.M+1)) := by
              apply Fin.ext
              show (k:ℕ) - L.wrapNB b - 1 + 1 = L.wrapNC a + 1
              omega
            rw [hps]
            exact hQ

/-- **The complementary (wrapping) arc** of a polygonal loop, as a polygonal loop. -/
noncomputable def PolyLoop.wrapArc (L : PolyLoop Ω) (hstrict : StrictMono L.t) (a b : I)
    (hval : L.loop a = L.loop b) : PolyLoop Ω where
  M := L.wrapM a b
  hM := by
    have h : L.wrapM a b = 2 + L.wrapNB b + L.wrapNC a := rfl
    omega
  base := L.loop a
  loop := L.wrapLoop a b hval
  t := L.wrapT a b
  ht0 := L.wrapT_zero a b
  ht1 := L.wrapT_last a b
  htmono := L.wrapT_mono hstrict a b
  haff := L.wrapT_affine hval

/-! ### Loops with at most two edges are null-homotopic -/

/-- A one-edge polygonal loop is constant. -/
lemma PolyLoop.loop_eq_of_M_eq_one (L : PolyLoop Ω) (h : L.M = 1) (s : I) :
    L.loop s = L.loop 0 := by
  have h0c : (⟨0, L.hM⟩ : Fin L.M).castSucc = 0 := by apply Fin.ext; simp
  have h0s : (⟨0, L.hM⟩ : Fin L.M).succ = Fin.last L.M := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    omega
  have hmain := L.haff ⟨0, L.hM⟩ s
  rw [h0c, h0s, L.ht0, L.ht1, Icc.convexComb_zero_one] at hmain
  have hbase : L.loop 1 = L.loop 0 := L.loop.target'.trans L.loop.source'.symm
  apply Subtype.ext
  rw [hmain, ← hbase]
  ring

lemma PolyLoop.homotopic_refl_of_M_eq_one (L : PolyLoop Ω) (h : L.M = 1) :
    L.loop.Homotopic (Path.refl L.base) := by
  have heq : L.loop = Path.refl L.base := by
    apply Path.ext
    funext s
    rw [L.loop_eq_of_M_eq_one h s, Path.refl_apply]
    exact L.loop.source'
  refine ⟨?c⟩
  rw [heq]
  exact Path.Homotopy.refl _

/-- A loop whose image lies in a convex subset of `Ω` containing the base point is null-homotopic. -/
lemma Path.homotopic_refl_of_convex_image {Ω : Set ℂ} {x : ↥Ω} (γ : Path x x) {C : Set ℂ}
    (hC : Convex ℝ C) (hsub : C ⊆ Ω) (hbase : ((x : ↥Ω) : ℂ) ∈ C)
    (hγ : ∀ s : I, ((γ s : ↥Ω) : ℂ) ∈ C) : γ.Homotopic (Path.refl x) := by
  refine ⟨ContinuousMap.HomotopyWith.mk
    (ContinuousMap.Homotopy.mk
      (⟨fun q : I × I => ⟨(1 - (q.1:ℝ)) • ((γ q.2 : ↥Ω) : ℂ) + (q.1:ℝ) • ((x : ↥Ω) : ℂ),
          hsub (hC (hγ q.2) hbase (by have := q.1.2.2; linarith) (by exact q.1.2.1)
            (by ring))⟩,
        by fun_prop⟩ : C(I × I, ↥Ω))
      (by
        intro t
        apply Subtype.ext
        show (1 - ((0:I):ℝ)) • ((γ t : ↥Ω) : ℂ) + ((0:I):ℝ) • ((x : ↥Ω) : ℂ)
          = ((γ t : ↥Ω) : ℂ)
        simp)
      (by
        intro t
        apply Subtype.ext
        show (1 - ((1:I):ℝ)) • ((γ t : ↥Ω) : ℂ) + ((1:I):ℝ) • ((x : ↥Ω) : ℂ)
          = (((Path.refl x) t : ↥Ω) : ℂ)
        rw [Path.refl_apply]
        simp))
    (by
      intro u t ht
      rcases ht with ht | ht
      · rw [ht]
        apply Subtype.ext
        show (1 - (u:ℝ)) • ((γ 0 : ↥Ω) : ℂ) + (u:ℝ) • ((x : ↥Ω) : ℂ) = ((γ 0 : ↥Ω) : ℂ)
        rw [show γ 0 = x from γ.source', ← add_smul, sub_add_cancel, one_smul]
      · rw [Set.mem_singleton_iff.mp ht]
        apply Subtype.ext
        show (1 - (u:ℝ)) • ((γ 1 : ↥Ω) : ℂ) + (u:ℝ) • ((x : ↥Ω) : ℂ) = ((γ 1 : ↥Ω) : ℂ)
        rw [show γ 1 = x from γ.target', ← add_smul, sub_add_cancel, one_smul])⟩

namespace PolyLoop

variable {Ω : Set ℂ}

/-- For a polygonal loop with at most two edges the whole image lies in the segment from the base
point to the second vertex. -/
lemma image_subset_segment_of_M_le_two (L : PolyLoop Ω) (h : L.M ≤ 2) (s : I) :
    ((L.loop s : ↥Ω) : ℂ) ∈ segment ℝ ((L.loop 0 : ↥Ω) : ℂ)
      ((L.loop (L.t (Fin.succ ⟨0, L.hM⟩)) : ↥Ω) : ℂ) := by
  rcases Nat.lt_or_ge L.M 2 with h1 | h2
  · have hMpos := L.hM
    have hM1 : L.M = 1 := by omega
    have hsucc : L.t (Fin.succ ⟨0, L.hM⟩) = 1 := by
      rw [show Fin.succ (⟨0, L.hM⟩ : Fin L.M) = Fin.last L.M from by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega, L.ht1]
    rw [L.loop_eq_of_M_eq_one hM1 s, hsucc]
    exact left_mem_segment ℝ _ _
  · have hMpos := L.hM
    have hM2 : L.M = 2 := by omega
    have hk1 : (1 : ℕ) < L.M := by omega
    set k₀ : Fin L.M := ⟨0, L.hM⟩ with hk0
    set k₁ : Fin L.M := ⟨1, hk1⟩ with hk1'
    have hk0c : k₀.castSucc = (0 : Fin (L.M+1)) := by apply Fin.ext; simp [hk0]
    have hk0s : k₀.succ = Fin.succ (⟨0, L.hM⟩ : Fin L.M) := rfl
    have hk1c : k₁.castSucc = Fin.succ (⟨0, L.hM⟩ : Fin L.M) := by
      apply Fin.ext
      show (k₁:ℕ) = 0 + 1
      rw [hk1']
    have hk1s : L.t k₁.succ = 1 := by
      rw [show k₁.succ = Fin.last L.M from by
        apply Fin.ext
        show (k₁:ℕ) + 1 = L.M
        rw [hk1']
        show ((1:ℕ) : ℕ) + 1 = L.M
        omega, L.ht1]
    have hbase : L.loop 1 = L.loop 0 := L.loop.target'.trans L.loop.source'.symm
    rcases le_total s (L.t k₀.succ) with hs | hs
    · obtain ⟨θ, hθ⟩ := Icc.exists_convexComb_eq (c := L.t k₀.castSucc) (d := L.t k₀.succ)
        (α := s) (by rw [show L.t k₀.castSucc = 0 from by rw [hk0c]; exact L.ht0]; exact s.2.1) hs
      rw [segment_eq_image]
      refine ⟨(θ:ℝ), ⟨θ.2.1, θ.2.2⟩, ?_⟩
      show (1 - (θ:ℝ)) • ((L.loop 0 : ↥Ω) : ℂ)
          + (θ:ℝ) • ((L.loop (L.t (Fin.succ ⟨0, L.hM⟩)) : ↥Ω) : ℂ) = ((L.loop s : ↥Ω) : ℂ)
      rw [← hθ, L.haff k₀ θ, hk0c, hk0s, L.ht0]
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    · obtain ⟨θ, hθ⟩ := Icc.exists_convexComb_eq (c := L.t k₁.castSucc) (d := L.t k₁.succ)
        (α := s) hs (by rw [hk1s]; exact s.2.2)
      rw [segment_eq_image]
      refine ⟨(1 - (θ:ℝ)), ⟨by linarith [θ.2.2], by linarith [θ.2.1]⟩, ?_⟩
      show (1 - (1 - (θ:ℝ))) • ((L.loop 0 : ↥Ω) : ℂ)
          + (1 - (θ:ℝ)) • ((L.loop (L.t (Fin.succ ⟨0, L.hM⟩)) : ↥Ω) : ℂ) = ((L.loop s : ↥Ω) : ℂ)
      rw [← hθ, L.haff k₁ θ, hk1c, hk1s, hbase]
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring

/-- The segment from the base point to the second vertex is contained in `Ω`. -/
lemma segment_subset_of_M_le_two (L : PolyLoop Ω) (h : L.M ≤ 2) :
    segment ℝ ((L.loop 0 : ↥Ω) : ℂ) ((L.loop (L.t (Fin.succ ⟨0, L.hM⟩)) : ↥Ω) : ℂ) ⊆ Ω := by
  intro z hz
  rcases Nat.lt_or_ge L.M 2 with h1 | h2
  · have hMpos := L.hM
    have hM1 : L.M = 1 := by omega
    have hsucc : L.t (Fin.succ ⟨0, L.hM⟩) = 1 := by
      rw [show Fin.succ (⟨0, L.hM⟩ : Fin L.M) = Fin.last L.M from by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega, L.ht1]
    have hbase : L.loop 1 = L.loop 0 := L.loop.target'.trans L.loop.source'.symm
    rw [hsucc, hbase, segment_same] at hz
    rw [Set.mem_singleton_iff.mp hz]
    exact (L.loop 0).2
  · have hMpos := L.hM
    have hM2 : L.M = 2 := by omega
    set k₀ : Fin L.M := ⟨0, L.hM⟩ with hk0
    have hk0c : k₀.castSucc = (0 : Fin (L.M+1)) := by apply Fin.ext; simp [hk0]
    have hk0s : k₀.succ = Fin.succ (⟨0, L.hM⟩ : Fin L.M) := rfl
    rw [segment_eq_image] at hz
    obtain ⟨θ, hθ, hz⟩ := hz
    rw [← hz]
    show (1 - θ) • ((L.loop 0 : ↥Ω) : ℂ)
        + θ • ((L.loop (L.t (Fin.succ ⟨0, L.hM⟩)) : ↥Ω) : ℂ) ∈ Ω
    rw [show (1 - θ) • ((L.loop 0 : ↥Ω) : ℂ)
          + θ • ((L.loop (L.t (Fin.succ ⟨0, L.hM⟩)) : ↥Ω) : ℂ)
        = ((L.loop (Icc.convexComb (L.t k₀.castSucc) (L.t k₀.succ) ⟨θ, hθ⟩) : ↥Ω) : ℂ) from by
      rw [L.haff k₀ ⟨θ, hθ⟩, hk0c, hk0s, L.ht0]
      rw [Complex.real_smul, Complex.real_smul]
      push_cast
      ring]
    exact (L.loop _).2

/-- A polygonal loop with at most two edges is null-homotopic. -/
lemma homotopic_refl_of_M_le_two (L : PolyLoop Ω) (h : L.M ≤ 2) :
    L.loop.Homotopic (Path.refl L.base) :=
  Path.homotopic_refl_of_convex_image L.loop (convex_segment _ _) (L.segment_subset_of_M_le_two h)
    (by
      have h : ((L.loop 0 : ↥Ω) : ℂ) = ((L.base : ↥Ω) : ℂ) :=
        congrArg (fun z : ↥Ω => (z : ℂ)) L.loop.source' 
      rw [← h]
      exact left_mem_segment ℝ _ _)
    (fun s => L.image_subset_segment_of_M_le_two h s)

end PolyLoop

/-! ### Helpers for the descent -/

/-- The composition of two paths that are both homotopic to the constant path is null-homotopic. -/
lemma Path.trans_const_eq_refl {Y : Type*} [TopologicalSpace Y] {a b c : Y}
    (hab : a = b) (hbc : b = c) :
    (((Path.refl a).cast rfl hab.symm).trans ((Path.refl b).cast rfl hbc.symm)).Homotopic
      ((Path.refl a).cast rfl (hab.trans hbc).symm) := by
  subst hab
  subst hbc
  exact Path.Homotopic.refl_trans _

/-- If both halves of a loop are null-homotopic, so is the loop. -/
lemma PolyLoop.homotopic_refl_of_subArcs (L : PolyLoop Ω) {b : I} (hb : 0 < b) (hb1 : b < 1)
    (hv0 : L.loop 0 = L.loop b) (hv1 : L.loop b = L.loop 1)
    (h1 : (L.subArc hb hv0).loop.Homotopic (Path.refl (L.subArc hb hv0).base))
    (h2 : (L.subArc hb1 hv1).loop.Homotopic (Path.refl (L.subArc hb1 hv1).base)) :
    L.loop.Homotopic (Path.refl L.base) := by
  have h1' : (L.loop.subpath 0 b).Homotopic ((Path.refl (L.loop 0)).cast rfl hv0.symm) := h1
  have h2' : (L.loop.subpath b 1).Homotopic ((Path.refl (L.loop b)).cast rfl hv1.symm) := h2
  have hA : ((L.loop.subpath 0 b).trans (L.loop.subpath b 1)).Homotopic
      (((Path.refl (L.loop 0)).cast rfl hv0.symm).trans
        ((Path.refl (L.loop b)).cast rfl hv1.symm)) := Path.Homotopic.hcomp h1' h2'
  have hB : ((L.loop.subpath 0 b).trans (L.loop.subpath b 1)).Homotopic
      ((Path.refl (L.loop 0)).cast rfl (hv0.trans hv1).symm) :=
    hA.trans (Path.trans_const_eq_refl hv0 hv1)
  have hC : (L.loop.subpath 0 1).Homotopic
      ((Path.refl (L.loop 0)).cast rfl (hv0.trans hv1).symm) :=
    (Path.Homotopic.symm ⟨Path.Homotopy.subpathTransSubpath L.loop 0 b 1⟩).trans hB
  have hD : (L.loop.cast L.loop.source' L.loop.target').Homotopic
      ((Path.refl (L.loop 0)).cast rfl (hv0.trans hv1).symm) := by
    rw [← L.subpath_zero_one']
    exact hC
  have hE : ((Path.refl (L.loop 0)).cast rfl (hv0.trans hv1).symm).cast L.loop.source'.symm
      L.loop.target'.symm = Path.refl L.base := by
    apply Path.ext
    funext t
    rw [Path.cast_coe, Path.cast_coe, Path.refl_apply]
    exact L.loop.source'
  have hF : L.loop.Homotopic (((Path.refl (L.loop 0)).cast rfl (hv0.trans hv1).symm).cast
      L.loop.source'.symm L.loop.target'.symm) := by
    have h5 := (Path.Homotopic.cast_iff (γ := L.loop.cast L.loop.source' L.loop.target')
      (δ := (Path.refl (L.loop 0)).cast rfl (hv0.trans hv1).symm)
      L.loop.source'.symm L.loop.target'.symm).mpr hD
    rwa [Path.cast_cast_self] at h5
  rw [hE] at hF
  exact hF

/-- **The trichotomy for a point on two segments.** If `X` lies on the segments `[A,B]` and
`[B,C]` (with `X ≠ B`) then one of `A`, `C` lies on the segment joining the other to `B`. -/
lemma collinear_trichotomy {A B C X : ℂ} (hXB : X ≠ B)
    (hAB : X ∈ segment ℝ A B) (hBC : X ∈ segment ℝ B C) :
    A ∈ segment ℝ B C ∨ C ∈ segment ℝ A B := by
  by_cases hXA : X = A
  · left
    rw [← hXA]
    exact hBC
  by_cases hXC : X = C
  · right
    rw [← hXC]
    exact hAB
  rw [segment_eq_image] at hAB hBC
  obtain ⟨α, hα, hαX⟩ := hAB
  obtain ⟨β, hβ, hβX⟩ := hBC
  have hαX' : (1 - (α:ℂ)) * A + (α:ℂ) * B = X := by
    rw [← hαX]
    show (1 - (α:ℂ)) * A + (α:ℂ) * B = (1 - α) • A + α • B
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hβX' : (1 - (β:ℂ)) * B + (β:ℂ) * C = X := by
    rw [← hβX]
    show (1 - (β:ℂ)) * B + (β:ℂ) * C = (1 - β) • B + β • C
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    ring
  have hα1 : α ≠ 1 := by
    intro h
    subst h
    norm_num at hαX'
    exact hXB hαX'.symm
  have hβ0 : β ≠ 0 := by
    intro h
    subst h
    norm_num at hβX'
    exact hXB hβX'.symm
  have hβ0pos : 0 < β := lt_of_le_of_ne hβ.1 (Ne.symm hβ0)
  have hα1pos : 0 < 1 - α := sub_pos.mpr (lt_of_le_of_ne hα.2 hα1)
  have hα1' : (1 - (α:ℂ)) ≠ 0 := by
    intro h
    have h1 : (α:ℂ) = 1 := (sub_eq_zero.mp h).symm
    exact hα1 (by exact_mod_cast h1)
  have hβ0' : (β:ℂ) ≠ 0 := by exact_mod_cast hβ0
  rcases lt_or_ge (1:ℝ) (α + β) with hsum | hsum
  · right
    rw [segment_eq_image]
    refine ⟨(α + β - 1) / β, ⟨div_nonneg (by linarith) hβ.1, ?_⟩, ?_⟩
    · rw [div_le_one hβ0pos]
      linarith [hα.2]
    · have hkey : (β:ℂ) * C = (1 - (α:ℂ)) * A + ((α:ℂ) + (β:ℂ) - 1) * B := by
        have h2' : (β:ℂ) * C = X - (1 - (β:ℂ)) * B := by rw [← hβX']; ring
        rw [h2', ← hαX']
        ring
      have hgoal : (1 - ((α:ℂ) + (β:ℂ) - 1) / (β:ℂ)) * A
          + (((α:ℂ) + (β:ℂ) - 1) / (β:ℂ)) * B = (β:ℂ)⁻¹ * ((β:ℂ) * C) := by
        rw [hkey]
        field_simp
        ring
      show ((fun θ : ℝ => (1 - θ) • A + θ • B) ((α + β - 1) / β)) = C
      rw [show ((fun θ : ℝ => (1 - θ) • A + θ • B) ((α + β - 1) / β))
          = (1 - ((α:ℂ) + (β:ℂ) - 1) / (β:ℂ)) * A
            + (((α:ℂ) + (β:ℂ) - 1) / (β:ℂ)) * B from by
        show ((1 - (α + β - 1) / β) • A + ((α + β - 1) / β) • B)
          = (1 - ((α:ℂ) + (β:ℂ) - 1) / (β:ℂ)) * A
            + (((α:ℂ) + (β:ℂ) - 1) / (β:ℂ)) * B
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring]
      rw [hgoal, ← mul_assoc, inv_mul_cancel₀ hβ0', one_mul]
  · left
    rw [segment_eq_image]
    refine ⟨β / (1 - α), ⟨div_nonneg hβ.1 hα1pos.le, ?_⟩, ?_⟩
    · rw [div_le_one hα1pos]
      linarith
    · have hkey : (1 - (α:ℂ)) * A = X - (α:ℂ) * B := by rw [← hαX']; ring
      have hgoal : (1 - (α:ℂ)) * A
          = (1 - (α:ℂ)) * ((1 - (β:ℂ) / (1 - (α:ℂ))) * B
            + ((β:ℂ) / (1 - (α:ℂ))) * C) := by
        rw [hkey, ← hβX']
        field_simp
        ring
      show ((fun θ : ℝ => (1 - θ) • B + θ • C) (β / (1 - α))) = A
      rw [show ((fun θ : ℝ => (1 - θ) • B + θ • C) (β / (1 - α)))
          = (1 - (β:ℂ) / (1 - (α:ℂ))) * B + ((β:ℂ) / (1 - (α:ℂ))) * C from by
        show ((1 - β / (1 - α)) • B + (β / (1 - α)) • C)
          = (1 - (β:ℂ) / (1 - (α:ℂ))) * B + ((β:ℂ) / (1 - (α:ℂ))) * C
        rw [Complex.real_smul, Complex.real_smul]
        push_cast
        ring]
      exact (mul_left_cancel₀ hα1' hgoal).symm

/-! ### Dropping a stalled breakpoint -/

/-- The index map that drops the breakpoint `k+1`. -/
def PolyLoop.dropIdx (L : PolyLoop Ω) (k : Fin L.M) (j : Fin (L.M - 1 + 1)) : Fin (L.M + 1) :=
  ⟨if (j:ℕ) ≤ (k:ℕ) then (j:ℕ) else (j:ℕ) + 1, by
    have hj : (j:ℕ) ≤ L.M - 1 := Nat.lt_succ_iff.mp j.2
    have hMpos : 1 ≤ L.M := L.hM
    have hk := k.2
    split_ifs with h <;> omega⟩

lemma PolyLoop.dropIdx_val (L : PolyLoop Ω) (k : Fin L.M) (j : Fin (L.M - 1 + 1)) :
    ((L.dropIdx k j : Fin (L.M+1)) : ℕ) =
      if (j:ℕ) ≤ (k:ℕ) then (j:ℕ) else (j:ℕ) + 1 := rfl

lemma PolyLoop.dropIdx_mono (L : PolyLoop Ω) (k : Fin L.M) :
    Monotone (L.dropIdx k) := by
  intro a b hab
  have hab' : (a:ℕ) ≤ (b:ℕ) := hab
  rw [Fin.le_iff_val_le_val, L.dropIdx_val, L.dropIdx_val]
  split_ifs <;> omega

/-- Dropping a stalled breakpoint of a polygonal loop. -/
noncomputable def PolyLoop.dropT (L : PolyLoop Ω) (k : Fin L.M) (hk : L.t k.castSucc = L.t k.succ)
    (hM2 : 2 ≤ L.M) : PolyLoop Ω where
  M := L.M - 1
  hM := by omega
  base := L.base
  loop := L.loop
  t := fun j => L.t (L.dropIdx k j)
  ht0 := by
    rw [show L.dropIdx k 0 = (0 : Fin (L.M+1)) from by
      apply Fin.ext
      rw [L.dropIdx_val,
        if_pos (show ((0 : Fin (L.M - 1 + 1)) : ℕ) ≤ (k:ℕ) from Nat.zero_le _)]
      rfl,
      L.ht0]
  ht1 := by
    have hj : ((Fin.last (L.M - 1) : Fin (L.M - 1 + 1)) : ℕ) = L.M - 1 := by simp
    by_cases h : L.M - 1 ≤ (k:ℕ)
    · rw [show L.dropIdx k (Fin.last (L.M - 1)) = k.castSucc from by
        apply Fin.ext
        show ((L.dropIdx k (Fin.last (L.M - 1)) : Fin (L.M+1)) : ℕ) = (k.castSucc : Fin (L.M+1)).val
        rw [L.dropIdx_val, hj, if_pos h, Fin.val_castSucc]
        omega]
      rw [hk, show k.succ = Fin.last L.M from by
        apply Fin.ext; simp only [Fin.val_succ, Fin.val_last]; omega, L.ht1]
    · rw [show L.dropIdx k (Fin.last (L.M - 1)) = Fin.last L.M from by
        apply Fin.ext
        show ((L.dropIdx k (Fin.last (L.M - 1)) : Fin (L.M+1)) : ℕ) = (Fin.last L.M : Fin (L.M+1)).val
        rw [L.dropIdx_val, hj, if_neg h, Fin.val_last]
        omega]
      exact L.ht1
  htmono := fun a b hab => L.htmono (L.dropIdx_mono k hab)
  haff := by
    intro j u
    set jj := (j:ℕ) with hjj
    have hjle : jj ≤ L.M - 1 := le_of_lt j.2
    have hcs : j.castSucc = (⟨jj, by omega⟩ : Fin (L.M - 1 + 1)) := by apply Fin.ext; simp [hjj]
    have hsc : j.succ = (⟨jj + 1, by omega⟩ : Fin (L.M - 1 + 1)) := by apply Fin.ext; simp [hjj]
    have hcs' : L.dropIdx k j.castSucc = L.dropIdx k (⟨jj, by omega⟩ : Fin (L.M - 1 + 1)) :=
      congrArg _ hcs
    have hsc' : L.dropIdx k j.succ = L.dropIdx k (⟨jj + 1, by omega⟩ : Fin (L.M - 1 + 1)) :=
      congrArg _ hsc
    have hklt : (k:ℕ) < L.M := k.2
    by_cases hcase : jj + 1 ≤ (k:ℕ)
    · have h1 : L.dropIdx k j.castSucc = (⟨jj, by omega⟩ : Fin (L.M+1)) := by
        rw [hcs']
        apply Fin.ext
        rw [L.dropIdx_val,
          if_pos (show jj ≤ (k:ℕ) from by omega)]
      have h2 : L.dropIdx k j.succ = (⟨jj + 1, by omega⟩ : Fin (L.M+1)) := by
        rw [hsc']
        apply Fin.ext
        rw [L.dropIdx_val,
          if_pos (show jj + 1 ≤ (k:ℕ) from by omega)]
      rw [h1, h2]
      exact L.haff ⟨jj, by omega⟩ u
    · by_cases hcase2 : jj ≤ (k:ℕ)
      · have hkk : jj = (k:ℕ) := by omega
        have hidx1 : (⟨jj, by omega⟩ : Fin (L.M+1)) = k.castSucc := by
          apply Fin.ext
          show jj = (k.castSucc : Fin (L.M+1)).val
          rw [Fin.val_castSucc]
          exact hkk
        have hidx2 : (⟨jj + 1, by omega⟩ : Fin (L.M+1)) = k.succ := by
          apply Fin.ext
          show jj + 1 = (k.succ : Fin (L.M+1)).val
          rw [Fin.val_succ, hkk]
        have h1 : L.dropIdx k j.castSucc = (⟨jj, by omega⟩ : Fin (L.M+1)) := by
          rw [hcs']
          apply Fin.ext
          rw [L.dropIdx_val,
            if_pos (show jj ≤ (k:ℕ) from by omega)]
        have h2 : L.dropIdx k j.succ = (⟨jj + 2, by omega⟩ : Fin (L.M+1)) := by
          rw [hsc']
          apply Fin.ext
          rw [L.dropIdx_val,
            if_neg (show ¬ (jj + 1 ≤ (k:ℕ)) from by omega)]
        have hstall : L.t (⟨jj, by omega⟩ : Fin (L.M+1)) = L.t (⟨jj + 1, by omega⟩ : Fin (L.M+1)) :=
          (congrArg L.t hidx1).trans (hk.trans (congrArg L.t hidx2).symm)
        rw [h1, h2, hstall]
        exact L.haff ⟨jj + 1, by omega⟩ u
      · have h1 : L.dropIdx k j.castSucc = (⟨jj + 1, by omega⟩ : Fin (L.M+1)) := by
          rw [hcs']
          apply Fin.ext
          rw [L.dropIdx_val,
            if_neg (show ¬ (jj ≤ (k:ℕ)) from by omega)]
        have h2 : L.dropIdx k j.succ = (⟨jj + 2, by omega⟩ : Fin (L.M+1)) := by
          rw [hsc']
          apply Fin.ext
          rw [L.dropIdx_val,
            if_neg (show ¬ (jj + 1 ≤ (k:ℕ)) from by omega)]
        rw [h1, h2]
        exact L.haff ⟨jj + 1, by omega⟩ u

lemma PolyLoop.exists_eq_succ_of_not_strictMono (L : PolyLoop Ω) (h : ¬ StrictMono L.t) :
    ∃ k : Fin L.M, L.t k.castSucc = L.t k.succ := by
  by_contra hc
  push_neg at hc
  apply h
  intro a b hab
  have haM : (a:ℕ) < L.M := by have := a.2; have := b.2; omega
  have h1 : L.t a ≤ L.t (⟨(a:ℕ)+1, Nat.succ_lt_succ haM⟩ : Fin (L.M+1)) :=
    L.htmono (Fin.le_iff_val_le_val.mpr (by simp))
  have h2 : L.t a ≠ L.t (⟨(a:ℕ)+1, Nat.succ_lt_succ haM⟩ : Fin (L.M+1)) := by
    have h2' := hc ⟨(a:ℕ), haM⟩
    rwa [show (⟨(a:ℕ), haM⟩ : Fin L.M).castSucc = a from by apply Fin.ext; simp,
      show (⟨(a:ℕ), haM⟩ : Fin L.M).succ = (⟨(a:ℕ)+1, Nat.succ_lt_succ haM⟩ : Fin (L.M+1))
        from by apply Fin.ext; simp] at h2'
  have h3 : L.t (⟨(a:ℕ)+1, Nat.succ_lt_succ haM⟩ : Fin (L.M+1)) ≤ L.t b :=
    L.htmono (Fin.le_iff_val_le_val.mpr (by have := b.2; simp only [Fin.val_mk]; omega))
  exact lt_of_lt_of_le (lt_of_le_of_ne h1 h2) h3

/-- **The minimal polygonal loop has strictly increasing breakpoints.** -/
lemma PolyLoop.strictMono_of_isMin (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) : StrictMono L.t := by
  have hM2 : 2 ≤ L.M := by
    by_contra h
    have h1 : L.M = 1 := by have := L.hM; omega
    exact hL (L.homotopic_refl_of_M_eq_one h1)
  by_contra h
  obtain ⟨k, hk⟩ := L.exists_eq_succ_of_not_strictMono h
  have h' : (L.dropT k hk hM2).Essential := hL
  have := hmin _ h'
  have hM1 : (L.dropT k hk hM2).M = L.M - 1 := rfl
  omega

/-! ### Index computations for the minimal loop -/

lemma PolyLoop.gidx_t_castSucc (L : PolyLoop Ω) (hstrict : StrictMono L.t) (k : Fin L.M) :
    L.gidx (L.t k.castSucc) = k := by
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    have h1 : L.t (L.gidx (L.t k.castSucc)).castSucc ≤ L.t k.castSucc := L.gidx_le _
    have hcast : k.castSucc < (L.gidx (L.t k.castSucc)).castSucc := by
      apply Fin.lt_iff_val_lt_val.mpr
      exact hcon
    exact absurd (hstrict hcast) (not_lt.mpr h1)
  · exact Finset.le_max' _ _ (by
      rw [idxSet, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, le_rfl⟩)

lemma PolyLoop.gidx_t_succ (L : PolyLoop Ω) (hstrict : StrictMono L.t) (k : Fin L.M)
    (hk : (k:ℕ)+1 < L.M) :
    L.gidx (L.t k.succ) = ⟨(k:ℕ)+1, hk⟩ := by
  apply le_antisymm
  · by_contra hcon
    rw [not_le] at hcon
    have h1 : L.t (L.gidx (L.t k.succ)).castSucc ≤ L.t k.succ := L.gidx_le _
    have hcast : k.succ < (L.gidx (L.t k.succ)).castSucc := by
      apply Fin.lt_iff_val_lt_val.mpr
      simpa only [Fin.val_mk, Fin.val_succ, Fin.val_castSucc] using Fin.lt_iff_val_lt_val.mp hcon
    exact absurd (hstrict hcast) (not_lt.mpr h1)
  · apply Finset.le_max'
    rw [idxSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    show L.t k.succ ≤ L.t (⟨(k:ℕ)+1, hk⟩ : Fin L.M).castSucc
    rfl

lemma PolyLoop.gidx_one (L : PolyLoop Ω) : L.gidx 1 = ⟨L.M - 1, by have := L.hM; omega⟩ := by
  apply le_antisymm
  · exact Fin.le_iff_val_le_val.mpr (Nat.le_sub_one_of_lt (L.gidx 1).2)
  · apply Finset.le_max'
    rw [idxSet, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    exact L.t_le_one _

/-- The minimal loop has at least three edges. -/
lemma PolyLoop.three_le_of_isMin (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) : 3 ≤ L.M := by
  by_contra h
  have h2 : L.M ≤ 2 := by omega
  exact hL (L.homotopic_refl_of_M_le_two h2)

lemma PolyLoop.arcLen_interior (L : PolyLoop Ω) (hstrict : StrictMono L.t) {k : Fin L.M}
    (hklast : (k:ℕ) < L.M - 1) :
    L.arcLen (L.t k.castSucc) (L.t k.succ) = 1 := by
  have hkk : (k:ℕ)+1 < L.M := by omega
  unfold PolyLoop.arcLen
  rw [L.gidx_t_succ hstrict k hkk, L.gidx_t_castSucc hstrict k]
  have hif : L.t k.succ = L.t (⟨(k:ℕ)+1, hkk⟩ : Fin L.M).castSucc := rfl
  rw [if_pos hif]
  simp only [Fin.val_mk]
  omega

lemma PolyLoop.wrapM_interior (L : PolyLoop Ω) (hstrict : StrictMono L.t) {k : Fin L.M}
    (hk : 0 < (k:ℕ)) (hklast : (k:ℕ) < L.M - 1) :
    L.wrapM (L.t k.castSucc) (L.t k.succ) = L.M - 1 := by
  have hkk : (k:ℕ)+1 < L.M := by omega
  unfold PolyLoop.wrapM PolyLoop.wrapNB PolyLoop.wrapNC
  rw [L.gidx_t_succ hstrict k hkk, L.gidx_t_castSucc hstrict k]
  have hzero : ¬ ((k:ℕ) = 0) := by omega
  rw [if_neg hzero]
  have hif : L.t k.castSucc = L.t (⟨(k:ℕ), by have := k.2; omega⟩ : Fin L.M).castSucc := rfl
  rw [if_pos hif]
  simp only [Fin.val_mk]
  omega

/-- At least one of the two sub-arcs cut out by a double point touching the base point is
essential. -/
lemma PolyLoop.essential_or_sub_arcs (L : PolyLoop Ω) (hL : L.Essential) {b : I} (hb : 0 < b)
    (hb1 : b < 1) (hv0 : L.loop 0 = L.loop b) (hv1 : L.loop b = L.loop 1) :
    (L.subArc hb hv0).Essential ∨ (L.subArc hb1 hv1).Essential := by
  by_contra hc
  rw [not_or] at hc
  exact hL (L.homotopic_refl_of_subArcs hb hb1 hv0 hv1 (not_not.mp hc.1) (not_not.mp hc.2))

/-- **A minimal essential loop has no degenerate edge.** -/
lemma PolyLoop.no_degenerate_of_isMin (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) (hstrict : StrictMono L.t)
    (hM3 : 3 ≤ L.M) :
    ∀ k : Fin L.M, L.loop (L.t k.castSucc) ≠ L.loop (L.t k.succ) := by
  intro k heq
  have hMpos : 1 ≤ L.M := by have := L.hM; omega
  -- the "time" `t_{M-1}` is `< 1`
  have hlast_lt : L.t ((⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc) < 1 := by
    have h := hstrict (show (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc < Fin.last L.M from by
      apply Fin.lt_iff_val_lt_val.mpr
      simp only [Fin.val_castSucc, Fin.val_last, Fin.val_mk]
      omega)
    rwa [L.ht1] at h
  have hg0 : L.gidx (0 : I) = (⟨0, L.hM⟩ : Fin L.M) := by
    rw [← L.ht0]
    exact L.gidx_t_castSucc hstrict (⟨0, L.hM⟩ : Fin L.M)
  have hgK : L.gidx (L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1)))
      = ⟨L.M - 1, by have := L.hM; omega⟩ :=
    L.gidx_t_castSucc hstrict ⟨L.M - 1, by have := L.hM; omega⟩
  have hif_false : ¬ ((1 : I) = L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc) := by
    intro hcon
    rw [← hcon] at hlast_lt
    exact absurd hlast_lt (lt_irrefl _)
  have hif_true : L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1))
      = L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc := rfl
  rcases Nat.eq_zero_or_pos (k:ℕ) with hk0 | hkpos
  · -- the degenerate edge is the first one
    have hk_eq : k = ⟨0, L.hM⟩ := by apply Fin.ext; simp only [Fin.val_mk]; omega
    have ht1_pos : (0 : I) < L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc) := by
      rw [← L.ht0]
      exact hstrict (by
        apply Fin.lt_iff_val_lt_val.mpr
        simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]
        omega)
    have ht1_lt : L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc) < 1 := by
      have h := hstrict (show (⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc < Fin.last L.M from by
        apply Fin.lt_iff_val_lt_val.mpr
        simp only [Fin.val_castSucc, Fin.val_last, Fin.val_mk]
        omega)
      rwa [L.ht1] at h
    have h1 : L.t (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1)) = L.t k.succ := by
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_mk]
      omega
    have hv0 : L.loop 0 = L.loop (L.t (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1))) := by
      rw [h1, ← heq, hk_eq]
      rw [show ((⟨0, L.hM⟩ : Fin L.M).castSucc : Fin (L.M+1)) = 0 from by
        apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]]
      rw [L.ht0]
    have hv1 : L.loop (L.t (⟨1, by have := L.hM; omega⟩ : Fin (L.M+1))) = L.loop 1 := by
      rw [h1, ← heq, hk_eq]
      rw [show ((⟨0, L.hM⟩ : Fin L.M).castSucc : Fin (L.M+1)) = 0 from by
        apply Fin.ext; simp only [Fin.val_castSucc, Fin.val_mk, Fin.val_zero]]
      rw [L.ht0]
      exact L.loop.source'.trans L.loop.target'.symm
    have hM1 : (L.subArc ht1_pos hv0).M = 1 := by
      show L.arcLen 0 (L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc)) = 1
      have hg1 : L.gidx (L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc))
          = (⟨1, by have := L.hM; omega⟩ : Fin L.M) :=
        L.gidx_t_castSucc hstrict (⟨1, by have := L.hM; omega⟩ : Fin L.M)
      unfold PolyLoop.arcLen
      rw [hg1, hg0]
      rw [if_pos (show L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc)
          = L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc) from rfl)]
      simp only [Fin.val_mk]
    have hM2 : (L.subArc ht1_lt hv1).M = L.M - 1 := by
      show L.arcLen (L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc)) 1 = L.M - 1
      unfold PolyLoop.arcLen
      rw [L.gidx_one,
        show L.gidx (L.t ((⟨1, by have := L.hM; omega⟩ : Fin L.M).castSucc))
          = (⟨1, by have := L.hM; omega⟩ : Fin L.M) from
        L.gidx_t_castSucc hstrict (⟨1, by have := L.hM; omega⟩ : Fin L.M),
        if_neg hif_false]
      simp only [Fin.val_mk]
      omega
    rcases L.essential_or_sub_arcs hL ht1_pos ht1_lt hv0 hv1 with h1 | h1
    · have := hmin _ h1
      omega
    · have := hmin _ h1
      omega
  · by_cases hklast : (k:ℕ) = L.M - 1
    · -- the degenerate edge is the last one
      have hk_eq : k = ⟨L.M - 1, by have := L.hM; omega⟩ := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      have htK_pos : (0 : I) < L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1)) := by
        have hpos : (0 : Fin (L.M+1)) < (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1)) := by
          rw [Fin.lt_def]
          show (0:ℕ) < L.M - 1
          omega
        rw [← L.ht0]
        exact hstrict hpos
      have hks : L.t k.succ = 1 := by
        rw [show k.succ = Fin.last L.M from by
          apply Fin.ext; simp only [Fin.val_succ, Fin.val_last, Fin.val_mk]; omega, L.ht1]
      have hK : L.loop (L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1))) = L.loop 1 := by
        rw [← hks, ← heq]
        rw [show (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1)) = k.castSucc from by
          apply Fin.ext
          rw [Fin.val_castSucc]
          exact (congrArg Fin.val hk_eq).symm]
      have hv0 : L.loop 0 = L.loop (L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1))) := by
        rw [hK]
        exact L.loop.source'.trans L.loop.target'.symm
      have hv1 : L.loop (L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1))) = L.loop 1 := hK
      have hM1 : (L.subArc htK_pos hv0).M = L.M - 1 := by
        show L.arcLen 0 (L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1))) = L.M - 1
        unfold PolyLoop.arcLen
        rw [hgK, hg0, if_pos hif_true]
        simp only [Fin.val_mk]
        omega
      have hM2 : (L.subArc hlast_lt hv1).M = 1 := by
        show L.arcLen (L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin (L.M+1))) 1 = 1
        unfold PolyLoop.arcLen
        rw [L.gidx_one, hgK, if_neg hif_false]
        simp only [Fin.val_mk]
        omega
      rcases L.essential_or_sub_arcs hL htK_pos hlast_lt hv0 hv1 with h1 | h1
      · have := hmin _ h1
        omega
      · have := hmin _ h1
        omega
    · -- an interior degenerate edge
      have hklt : (k:ℕ) < L.M - 1 := by omega
      have harc : L.arcLen (L.t k.castSucc) (L.t k.succ) = 1 :=
        L.arcLen_interior hstrict hklt
      have hwrap' : L.wrapM (L.t k.castSucc) (L.t k.succ) = L.M - 1 :=
        L.wrapM_interior hstrict hkpos hklt
      have hlt : L.t k.castSucc < L.t k.succ := hstrict (by
        apply Fin.lt_iff_val_lt_val.mpr
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega)
      have hsub : (L.subArc hlt heq).loop.Homotopic (Path.refl (L.subArc hlt heq).base) :=
        (L.subArc hlt heq).homotopic_refl_of_M_eq_one harc
      rcases L.essential_or_wrap_of_double_point hL heq with h1 | h2
      · exact h1 hsub
      · have h2' : (L.wrapArc hstrict (L.t k.castSucc) (L.t k.succ) heq).Essential := h2
        have hle := hmin _ h2'
        rw [show (L.wrapArc hstrict (L.t k.castSucc) (L.t k.succ) heq).M
            = L.wrapM (L.t k.castSucc) (L.t k.succ) from rfl, hwrap'] at hle
        omega

/-! ### Structural facts about edges of a polygonal loop -/

/-- The image of a point of an edge lies on the segment spanned by the edge. -/
lemma PolyLoop.mem_segment_of_edge (L : PolyLoop Ω) (k : Fin L.M) {s : I}
    (h0 : L.t k.castSucc ≤ s) (h1 : s ≤ L.t k.succ) :
    ((L.loop s : ↥Ω) : ℂ) ∈ segment ℝ (((L.loop (L.t k.castSucc) : ↥Ω)) : ℂ)
      (((L.loop (L.t k.succ) : ↥Ω)) : ℂ) := by
  obtain ⟨x, hx⟩ := Icc.exists_convexComb_eq h0 h1
  rw [segment_eq_image]
  refine ⟨x, x.2, ?_⟩
  show (1 - (x:ℝ)) • (((L.loop (L.t k.castSucc) : ↥Ω)) : ℂ)
      + (x:ℝ) • (((L.loop (L.t k.succ) : ↥Ω)) : ℂ) = ((L.loop s : ↥Ω) : ℂ)
  rw [← hx, L.haff k x, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- Every point of the segment spanned by an edge is the image of a time of that edge. -/
lemma PolyLoop.exists_eq_of_mem_segment (L : PolyLoop Ω) (k : Fin L.M) {Y : ℂ}
    (hY : Y ∈ segment ℝ (((L.loop (L.t k.castSucc) : ↥Ω)) : ℂ)
      (((L.loop (L.t k.succ) : ↥Ω)) : ℂ)) :
    ∃ u : I, L.t k.castSucc ≤ u ∧ u ≤ L.t k.succ ∧ ((L.loop u : ↥Ω) : ℂ) = Y := by
  rw [segment_eq_image] at hY
  obtain ⟨θ, hθ, hθY⟩ := hY
  have hmono : L.t k.castSucc ≤ L.t k.succ := L.htmono (Fin.castSucc_le_succ k)
  refine ⟨Icc.convexComb (L.t k.castSucc) (L.t k.succ) ⟨θ, hθ⟩, Icc.le_convexComb hmono ⟨θ, hθ⟩,
    Icc.convexComb_le hmono ⟨θ, hθ⟩, ?_⟩
  have hval := L.haff k (⟨θ, hθ⟩ : I)
  rw [hval]
  have hβ : (fun θ : ℝ => (1 - θ) • (((L.loop (L.t k.castSucc) : ↥Ω)) : ℂ)
      + θ • (((L.loop (L.t k.succ) : ↥Ω)) : ℂ)) θ
      = (1 - θ) • (((L.loop (L.t k.castSucc) : ↥Ω)) : ℂ)
        + θ • (((L.loop (L.t k.succ) : ↥Ω)) : ℂ) := rfl
  rw [← hθY, hβ, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

/-- The index of a time lying (strictly) inside an edge. -/
lemma PolyLoop.gidx_eq_of_lt (L : PolyLoop Ω) {k : Fin L.M} {a : I}
    (h0 : L.t k.castSucc ≤ a) (h1 : a < L.t k.succ) : L.gidx a = k := by
  refine le_antisymm ?_ (Finset.le_max' _ _ ?_)
  · by_contra hcon
    rw [not_le] at hcon
    have hlt : (k : ℕ) < (L.gidx a : ℕ) := Fin.lt_def.mp hcon
    have h2 : L.t k.succ ≤ L.t (L.gidx a).castSucc := by
      apply L.htmono
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    exact absurd (h2.trans (L.gidx_le a)) (not_le.mpr h1)
  · rw [idxSet, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h0⟩

/-- The index of the last breakpoint time. -/
lemma PolyLoop.gidx_t_succ_last (L : PolyLoop Ω) (k : Fin L.M) (hk : (k : ℕ) + 1 = L.M) :
    L.gidx (L.t k.succ) = ⟨L.M - 1, by have := L.hM; omega⟩ := by
  have h1 : L.t k.succ = 1 := by
    have h2 : k.succ = Fin.last L.M := by
      apply Fin.ext
      simp only [Fin.val_succ, Fin.val_last]
      omega
    rw [h2, L.ht1]
  rw [h1, L.gidx_one]

/-- The number of edges of a full edge is one. -/
lemma PolyLoop.arcLen_castSucc_succ (L : PolyLoop Ω) (hstrict : StrictMono L.t) (k : Fin L.M) :
    L.arcLen (L.t k.castSucc) (L.t k.succ) = 1 := by
  by_cases hk : (k : ℕ) + 1 < L.M
  · unfold PolyLoop.arcLen
    rw [L.gidx_t_succ hstrict k hk, L.gidx_t_castSucc hstrict k]
    rw [if_pos (show L.t k.succ = L.t (⟨(k:ℕ)+1, hk⟩ : Fin L.M).castSucc from rfl)]
    simp only [Fin.val_mk]
    omega
  · have hk' : (k : ℕ) + 1 = L.M := by have := k.2; omega
    unfold PolyLoop.arcLen
    rw [L.gidx_t_castSucc hstrict k, L.gidx_t_succ_last k hk']
    rw [if_neg ?_]
    · simp only [Fin.val_mk]
      omega
    · intro hc
      have h1 : L.t k.succ = 1 := by
        have h2 : k.succ = Fin.last L.M := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          omega
        rw [h2, L.ht1]
      have h3 : L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc < 1 := by
        have h4 := hstrict (show (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc
            < Fin.last L.M from by
          apply Fin.lt_def.mpr
          simp only [Fin.val_castSucc, Fin.val_last, Fin.val_mk]
          omega)
        rwa [L.ht1] at h4
      rw [h1] at hc
      exact absurd hc.symm (ne_of_lt h3)

/-- Subadditivity of the edge count. -/
lemma PolyLoop.arcLen_add_le (L : PolyLoop Ω) {a b c : I} (hab : a ≤ b) (hbc : b ≤ c) :
    L.arcLen a c ≤ L.arcLen a b + L.arcLen b c := by
  have h1 : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab
  have h2 : (L.gidx b : ℕ) ≤ (L.gidx c : ℕ) := L.gidx_mono hbc
  have hX : (if c = L.t (L.gidx c).castSucc then 0 else 1) ≤ 1 := by split <;> omega
  show (L.gidx c : ℕ) - (L.gidx a : ℕ) + (if c = L.t (L.gidx c).castSucc then 0 else 1)
      ≤ (L.gidx b : ℕ) - (L.gidx a : ℕ) + (if b = L.t (L.gidx b).castSucc then 0 else 1)
        + ((L.gidx c : ℕ) - (L.gidx b : ℕ) + (if c = L.t (L.gidx c).castSucc then 0 else 1))
  omega

/-- The part of an edge before a given time has at most one edge. -/
lemma PolyLoop.arcLen_le_one_left (L : PolyLoop Ω) (hstrict : StrictMono L.t) {k : Fin L.M}
    {x : I} (h0 : L.t k.castSucc ≤ x) (h1 : x ≤ L.t k.succ) :
    L.arcLen (L.t k.castSucc) x ≤ 1 := by
  rcases eq_or_lt_of_le h1 with hx | hx
  · rw [hx]
    exact le_of_eq (L.arcLen_castSucc_succ hstrict k)
  · unfold PolyLoop.arcLen
    rw [L.gidx_eq_of_lt h0 hx, L.gidx_t_castSucc hstrict k]
    split <;> omega

/-- The part of an edge after a given time has at most one edge. -/
lemma PolyLoop.arcLen_le_one_right (L : PolyLoop Ω) (hstrict : StrictMono L.t) {k : Fin L.M}
    {x : I} (h0 : L.t k.castSucc ≤ x) (h1 : x ≤ L.t k.succ) :
    L.arcLen x (L.t k.succ) ≤ 1 := by
  rcases eq_or_lt_of_le h0 with hx | hx
  · rw [← hx]
    exact le_of_eq (L.arcLen_castSucc_succ hstrict k)
  · by_cases hx1 : x = L.t k.succ
    · rw [hx1]
      unfold PolyLoop.arcLen
      split <;> omega
    · have hgx : L.gidx x = k := L.gidx_eq_of_lt h0 (lt_of_le_of_ne h1 hx1)
      by_cases hk : (k : ℕ) + 1 < L.M
      · unfold PolyLoop.arcLen
        rw [hgx, L.gidx_t_succ hstrict k hk,
          if_pos (show L.t k.succ = L.t (⟨(k:ℕ)+1, hk⟩ : Fin L.M).castSucc from rfl)]
        simp only [Fin.val_mk]
        omega
      · have hk' : (k : ℕ) + 1 = L.M := by have := k.2; omega
        unfold PolyLoop.arcLen
        rw [hgx, L.gidx_t_succ_last k hk']
        split <;> omega

/-- The `wrapNC` value at a vertex. -/
lemma PolyLoop.wrapNC_castSucc (L : PolyLoop Ω) (hstrict : StrictMono L.t) (k : Fin L.M) :
    L.wrapNC (L.t k.castSucc) = (k : ℕ) - 1 := by
  unfold PolyLoop.wrapNC
  rw [L.gidx_t_castSucc hstrict k]
  by_cases hk : (k : ℕ) = 0
  · rw [if_pos hk]
    simp [hk]
  · rw [if_neg hk, if_pos rfl]
    simp

/-- A minimal essential polygonal loop has no double point whose two cut arcs both have fewer
edges than the loop itself. -/
theorem PolyLoop.no_double_point_of_lt (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) (hstrict : StrictMono L.t)
    {a b : I} (hab : a < b) (hval : L.loop a = L.loop b)
    (h1 : L.arcLen a b < L.M) (h2 : L.wrapM a b < L.M) : False := by
  rcases L.essential_or_wrap_of_double_point hL hval with h | h
  · have hh : (L.subArc hab hval).Essential := h
    have hle := hmin _ hh
    rw [show (L.subArc hab hval).M = L.arcLen a b from rfl] at hle
    omega
  · have hh : (L.wrapArc hstrict a b hval).Essential := h
    have hle := hmin _ hh
    rw [show (L.wrapArc hstrict a b hval).M = L.wrapM a b from rfl] at hle
    omega

/-- A polygonal loop with three edges whose base point lies on the middle edge is
null-homotopic. -/
lemma PolyLoop.homotopic_refl_of_M_eq_three (L : PolyLoop Ω) (h3 : L.M = 3)
    (hbase : ((L.base : ↥Ω) : ℂ) ∈ segment ℝ
      (((L.loop (L.t (⟨1, by omega⟩ : Fin L.M).castSucc) : ↥Ω)) : ℂ)
      (((L.loop (L.t (⟨1, by omega⟩ : Fin L.M).succ) : ↥Ω)) : ℂ)) :
    L.loop.Homotopic (Path.refl L.base) := by
  set kk : Fin L.M := ⟨1, by omega⟩ with hkk
  set P : ℂ := ((L.loop (L.t kk.castSucc) : ↥Ω) : ℂ) with hP
  set Q : ℂ := ((L.loop (L.t kk.succ) : ↥Ω) : ℂ) with hQ
  have hbPQ : ((L.base : ↥Ω) : ℂ) ∈ segment ℝ P Q := hbase
  refine Path.homotopic_refl_of_convex_image L.loop (convex_segment P Q) ?_ hbPQ ?_
  · intro y hy
    rw [segment_eq_image] at hy
    obtain ⟨θ, hθ, hθy⟩ := hy
    have hval := L.haff kk (⟨θ, hθ⟩ : I)
    have hred : (fun θ : ℝ => (1 - θ) • P + θ • Q) θ = (1 - θ) • P + θ • Q := rfl
    rw [← hθy, hred, hP, hQ, Complex.real_smul, Complex.real_smul]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Subtype.coe_mk] at hval ⊢
    rw [← hval]
    exact (L.loop (Icc.convexComb (L.t kk.castSucc) (L.t kk.succ) (⟨θ, hθ⟩ : I))).2
  · intro s
    have hs := L.mem_segment_of_edge (L.gidx s) (L.gidx_le s) (le_gidx_succ L s)
    set m := (L.gidx s : ℕ) with hm
    have hm2 : m ≤ 2 := by have := (L.gidx s).2; omega
    interval_cases m
    · have hge : (L.gidx s : ℕ) = 0 := by omega
      have h1 : (L.gidx s).castSucc = (0 : Fin (L.M+1)) := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_zero]
        omega
      have h2 : (L.gidx s).succ = kk.castSucc := by
        apply Fin.ext
        rw [hkk]
        simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_mk]
        omega
      have he1 : ((L.loop (L.t (L.gidx s).castSucc) : ↥Ω) : ℂ) = ((L.base : ↥Ω) : ℂ) := by
        rw [h1, L.ht0]
        exact congrArg (fun z : ↥Ω => (z : ℂ)) L.loop.source'
      have he2 : ((L.loop (L.t (L.gidx s).succ) : ↥Ω) : ℂ) = P := by
        rw [h2, hP]
      rw [he1, he2] at hs
      exact (convex_segment P Q).segment_subset hbPQ (left_mem_segment ℝ P Q) hs
    · have hge : (L.gidx s : ℕ) = 1 := by omega
      have h1 : (L.gidx s).castSucc = kk.castSucc := by
        apply Fin.ext
        rw [hkk]
        simp only [Fin.val_castSucc, Fin.val_mk]
        omega
      have h2 : (L.gidx s).succ = kk.succ := by
        apply Fin.ext
        rw [hkk]
        simp only [Fin.val_succ, Fin.val_mk]
        omega
      have he1 : ((L.loop (L.t (L.gidx s).castSucc) : ↥Ω) : ℂ) = P := by rw [h1, hP]
      have he2 : ((L.loop (L.t (L.gidx s).succ) : ↥Ω) : ℂ) = Q := by rw [h2, hQ]
      rwa [he1, he2] at hs
    · have hge : (L.gidx s : ℕ) = 2 := by omega
      have h1 : (L.gidx s).castSucc = kk.succ := by
        apply Fin.ext
        rw [hkk]
        simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_mk]
        omega
      have h2 : (L.gidx s).succ = Fin.last L.M := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_last]
        omega
      have he1 : ((L.loop (L.t (L.gidx s).castSucc) : ↥Ω) : ℂ) = Q := by rw [h1, hQ]
      have he2 : ((L.loop (L.t (L.gidx s).succ) : ↥Ω) : ℂ) = ((L.base : ↥Ω) : ℂ) := by
        rw [h2, L.ht1]
        exact congrArg (fun z : ↥Ω => (z : ℂ)) L.loop.target'
      rw [he1, he2] at hs
      exact (convex_segment P Q).segment_subset (right_mem_segment ℝ P Q) hbPQ hs

/-! ### An affine parametrization fact and index helpers -/

/-- Two times in one edge with equal image coincide (for a nondegenerate edge). -/
lemma PolyLoop.eq_of_loop_eq_on_edge (L : PolyLoop Ω) {k : Fin L.M}
    (hnd : L.loop (L.t k.castSucc) ≠ L.loop (L.t k.succ)) {x y : I}
    (hx0 : L.t k.castSucc ≤ x) (hx1 : x ≤ L.t k.succ)
    (hy0 : L.t k.castSucc ≤ y) (hy1 : y ≤ L.t k.succ) (h : L.loop x = L.loop y) : x = y := by
  obtain ⟨s, hs⟩ := Icc.exists_convexComb_eq (c := L.t k.castSucc) (d := L.t k.succ) (α := x) hx0 hx1
  obtain ⟨t, ht⟩ := Icc.exists_convexComb_eq (c := L.t k.castSucc) (d := L.t k.succ) (α := y) hy0 hy1
  have haffs := L.haff k s
  have hafft := L.haff k t
  have hst : s = t := by
    by_contra hne
    have hst' : (s:ℝ) ≠ (t:ℝ) := fun hh => hne (Subtype.ext hh)
    have h1 : (1 - (s:ℝ)) * (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ))
        + (s:ℝ) * (((L.loop (L.t k.succ) : ↥Ω) : ℂ))
        = (1 - (t:ℝ)) * (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ))
          + (t:ℝ) * (((L.loop (L.t k.succ) : ↥Ω) : ℂ)) := by
      rw [← haffs, ← hafft]
      exact (congrArg (fun z : ↥Ω => (z:ℂ)) ((congrArg L.loop hs).trans h)).trans
        (congrArg (fun z : ↥Ω => (z:ℂ)) (congrArg L.loop ht).symm)
    have hkey : (((s:ℝ) - (t:ℝ)) : ℂ) * ((((L.loop (L.t k.succ) : ↥Ω) : ℂ))
        - (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ))) = 0 := by
      have hgroup : ((1 - (s:ℝ)) * (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ))
          + (s:ℝ) * (((L.loop (L.t k.succ) : ↥Ω) : ℂ)))
          - ((1 - (t:ℝ)) * (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ))
            + (t:ℝ) * (((L.loop (L.t k.succ) : ↥Ω) : ℂ)))
          = (((s:ℝ) - (t:ℝ)) : ℂ) * ((((L.loop (L.t k.succ) : ↥Ω) : ℂ))
            - (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ))) := by ring
      rw [← hgroup, h1, sub_self]
    have h0' : (((s:ℝ) - (t:ℝ)) : ℂ) ≠ 0 := by
      intro hh
      have hh2 : ((s:ℝ) : ℂ) = ((t:ℝ) : ℂ) := sub_eq_zero.mp hh
      exact hst' (Complex.ofReal_injective hh2)
    have hAB : (((L.loop (L.t k.succ) : ↥Ω) : ℂ))
        = (((L.loop (L.t k.castSucc) : ↥Ω) : ℂ)) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left h0')
    exact hnd (Subtype.ext hAB.symm)
  rw [← hs, ← ht, hst]


/-- Two times in the same edge with equal image coincide (for a nondegenerate edge). -/
lemma PolyLoop.eq_of_same_edge (L : PolyLoop Ω) {x y : I} (hxy : L.gidx x = L.gidx y)
    (hnd : L.loop (L.t (L.gidx x).castSucc) ≠ L.loop (L.t (L.gidx x).succ))
    (h : L.loop x = L.loop y) : x = y := by
  obtain ⟨s, hs⟩ := Icc.exists_convexComb_eq (c := L.t (L.gidx x).castSucc)
    (d := L.t (L.gidx x).succ) (α := x) (L.gidx_le x) (le_gidx_succ L x)
  obtain ⟨t, ht⟩ := Icc.exists_convexComb_eq (c := L.t (L.gidx x).castSucc)
    (d := L.t (L.gidx x).succ) (α := y) (by rw [hxy]; exact L.gidx_le y)
    (by rw [hxy]; exact le_gidx_succ L y)
  have haffs := L.haff (L.gidx x) s
  have hafft := L.haff (L.gidx x) t
  have hst : s = t := by
    by_contra hne
    have hst' : (s:ℝ) ≠ (t:ℝ) := fun hh => hne (Subtype.ext hh)
    have h1 : (1 - (s:ℝ)) * (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ))
        + (s:ℝ) * (((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ))
        = (1 - (t:ℝ)) * (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ))
          + (t:ℝ) * (((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ)) := by
      rw [← haffs, ← hafft]
      exact (congrArg (fun z : ↥Ω => (z:ℂ)) ((congrArg L.loop hs).trans h)).trans
        (congrArg (fun z : ↥Ω => (z:ℂ)) (congrArg L.loop ht).symm)
    have hkey : (((s:ℝ) - (t:ℝ)) : ℂ) * ((((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ))
        - (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ))) = 0 := by
      have hgroup : ((1 - (s:ℝ)) * (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ))
          + (s:ℝ) * (((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ)))
          - ((1 - (t:ℝ)) * (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ))
            + (t:ℝ) * (((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ)))
          = (((s:ℝ) - (t:ℝ)) : ℂ) * ((((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ))
            - (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ))) := by ring
      rw [← hgroup, h1, sub_self]
    have h0' : (((s:ℝ) - (t:ℝ)) : ℂ) ≠ 0 := by
      intro hh
      have hh2 : ((s:ℝ) : ℂ) = ((t:ℝ) : ℂ) := sub_eq_zero.mp hh
      exact hst' (Complex.ofReal_injective hh2)
    have hAB : (((L.loop (L.t (L.gidx x).succ) : ↥Ω) : ℂ))
        = (((L.loop (L.t (L.gidx x).castSucc) : ↥Ω) : ℂ)) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hkey).resolve_left h0')
    exact hnd (Subtype.ext hAB.symm)
  rw [← hs, ← ht, hst]

/-- A time whose index is `k` and which is at most the vertex `t_k` equals that vertex. -/
lemma PolyLoop.eq_castSucc_of_gidx_eq (L : PolyLoop Ω) {u : I} {k : Fin L.M}
    (h : L.gidx u = k) (hle : u ≤ L.t k.castSucc) : u = L.t k.castSucc := by
  have h1 : L.t (L.gidx u).castSucc ≤ u := L.gidx_le u
  rw [h] at h1
  exact le_antisymm hle h1

/-- A time whose index is `k` and which is at least the vertex `t_{k+1}` equals that vertex. -/
lemma PolyLoop.eq_succ_of_gidx_eq (L : PolyLoop Ω) {u : I} {k : Fin L.M}
    (h : L.gidx u = k) (hle : L.t k.succ ≤ u) : u = L.t k.succ := by
  have h1 : u ≤ L.t (L.gidx u).succ := le_gidx_succ L u
  rw [h] at h1
  exact le_antisymm h1 hle

/-- `wrapNC` vanishes at a time that does not pass the first positive vertex. -/
lemma PolyLoop.wrapNC_eq_zero_of_le_vertex_one (L : PolyLoop Ω) (hstrict : StrictMono L.t)
    (hM2 : 2 ≤ L.M) {u : I}
    (hup : u ≤ L.t (⟨1, by omega⟩ : Fin L.M).castSucc) : L.wrapNC u = 0 := by
  by_cases h0 : (L.gidx u : ℕ) = 0
  · unfold PolyLoop.wrapNC
    rw [if_pos h0]
  · have hgu : L.gidx u = ⟨1, by omega⟩ := by
      have hle : (L.gidx u : ℕ) ≤ 1 := by
        have h1 : L.gidx u ≤ L.gidx (L.t (⟨1, by omega⟩ : Fin L.M).castSucc) :=
          L.gidx_mono hup
        rw [L.gidx_t_castSucc hstrict] at h1
        exact Fin.le_iff_val_le_val.mp h1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    have hu : u = L.t (⟨1, by omega⟩ : Fin L.M).castSucc := by
      have h1 : L.t (L.gidx u).castSucc ≤ u := L.gidx_le u
      rw [hgu] at h1
      exact le_antisymm hup h1
    rw [hu, L.wrapNC_castSucc hstrict (⟨1, by omega⟩ : Fin L.M)]
    simp

/-- **Forward case of the double-point analysis.**  If the arc from `a` to `b` is as long as
the whole loop, the double point `(a, b)` is the trivial one `(0, 1)`. -/
theorem PolyLoop.forward_case (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) (hstrict : StrictMono L.t)
    (hM3 : 3 ≤ L.M) (hnodeg : ∀ k : Fin L.M, L.loop (L.t k.castSucc) ≠ L.loop (L.t k.succ))
    {a b : I} (hab : a < b) (hval : L.loop a = L.loop b) (hE1 : L.M ≤ L.arcLen a b) :
    a = 0 ∧ b = 1 := by
  have hM2 : 2 ≤ L.M := by omega
  have hi_le_hj : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab.le
  have hj_le : (L.gidx b : ℕ) ≤ L.M - 1 := by have := (L.gidx b).2; omega
  have hd : (if b = L.t (L.gidx b).castSucc then 0 else 1) ≤ 1 := by split <;> omega
  have hE1'' : L.M ≤ (L.gidx b : ℕ) - (L.gidx a : ℕ)
      + (if b = L.t (L.gidx b).castSucc then 0 else 1) := hE1
  have hE1' : (L.gidx b : ℕ) - (L.gidx a : ℕ)
      + (if b = L.t (L.gidx b).castSucc then 0 else 1) = L.M := le_antisymm (by omega) hE1''
  have hia : (L.gidx a : ℕ) = 0 := by omega
  have hjb : (L.gidx b : ℕ) = L.M - 1 := by omega
  have hdb_eq : (if b = L.t (L.gidx b).castSucc then 0 else 1) = 1 := by omega
  have hga : L.gidx a = ⟨0, L.hM⟩ := by apply Fin.ext; omega
  have hgb : L.gidx b = ⟨L.M - 1, by have := L.hM; omega⟩ := by apply Fin.ext; omega
  have hdb : ¬ (b = L.t (L.gidx b).castSucc) := by
    intro hc
    rw [if_pos hc] at hdb_eq
    omega
  by_cases ha0 : a = 0
  · refine ⟨ha0, ?_⟩
    have hX : L.loop b = L.loop 1 := by
      rw [← hval, ha0]
      exact L.loop.source'.trans L.loop.target'.symm
    have hgy : L.gidx b = L.gidx 1 := by rw [hgb, L.gidx_one]
    exact L.eq_of_same_edge hgy (hnodeg (L.gidx b)) hX
  · exfalso
    set k0 : Fin L.M := ⟨0, L.hM⟩ with hk0
    set kA : Fin L.M := ⟨L.M - 1, by have := L.hM; omega⟩ with hkA
    have hgak : L.gidx a = k0 := by rw [hk0]; exact hga
    have hgbk : L.gidx b = kA := by rw [hkA]; exact hgb
    have hga_le : L.t k0.castSucc ≤ a := by rw [← hgak]; exact L.gidx_le a
    have hga_ge : a ≤ L.t k0.succ := by rw [← hgak]; exact le_gidx_succ L a
    have hgb_le : L.t kA.castSucc ≤ b := by rw [← hgbk]; exact L.gidx_le b
    have hgb_ge : b ≤ L.t kA.succ := by rw [← hgbk]; exact le_gidx_succ L b
    have hkAv : (kA : ℕ) = L.M - 1 := by simp [hkA]
    have hk0v : (k0 : ℕ) = 0 := by simp [hk0]
    have hkAsucc : L.t kA.succ = (1 : I) := by
      have h2 : kA.succ = Fin.last L.M := by
        apply Fin.ext
        simp only [Fin.val_succ, Fin.val_last, Fin.val_mk]
        rw [hkA]
        simp only [Fin.val_mk]
        omega
      rw [h2, L.ht1]
    have hk0cast : L.t k0.castSucc = (0 : I) := by
      have h3 : k0.castSucc = (0 : Fin (L.M+1)) := by
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_mk]
        rw [hk0]
      rw [h3, L.ht0]
    have hk0succ : L.t k0.succ = L.t (⟨1, by omega⟩ : Fin L.M).castSucc := rfl
    have hXB : ((L.loop a : ↥Ω) : ℂ) ≠ ((L.loop (L.t k0.castSucc) : ↥Ω) : ℂ) := by
      intro hc
      have hgy : L.gidx a = L.gidx (L.t k0.castSucc) := by
        rw [hgak, L.gidx_t_castSucc hstrict k0]
      have heq : a = L.t k0.castSucc := L.eq_of_same_edge hgy (hnodeg (L.gidx a)) (Subtype.ext hc)
      exact ha0 (heq.trans hk0cast)
    have hmemA : ((L.loop a : ↥Ω) : ℂ) ∈ segment ℝ (((L.loop (L.t kA.castSucc) : ↥Ω)) : ℂ)
        (((L.loop (L.t kA.succ) : ↥Ω)) : ℂ) := by
      have h := L.mem_segment_of_edge kA hgb_le hgb_ge
      rw [← hval] at h
      exact h
    have hsec : (((L.loop (L.t kA.succ) : ↥Ω)) : ℂ)
        = (((L.loop (L.t k0.castSucc) : ↥Ω)) : ℂ) := by
      rw [hkAsucc, hk0cast]
      exact congrArg (fun z : ↥Ω => (z : ℂ)) (L.loop.target'.trans L.loop.source'.symm)
    rw [hsec] at hmemA
    have hmemB : ((L.loop a : ↥Ω) : ℂ) ∈ segment ℝ (((L.loop (L.t k0.castSucc) : ↥Ω)) : ℂ)
        (((L.loop (L.t k0.succ) : ↥Ω)) : ℂ) := L.mem_segment_of_edge k0 hga_le hga_ge
    rcases collinear_trichotomy hXB hmemA hmemB with hAlt | hAlt
    · obtain ⟨u, hu0, hu1, huval⟩ := L.exists_eq_of_mem_segment k0 hAlt
      have huval' : L.loop u = L.loop (L.t kA.castSucc) := Subtype.ext huval
      have hsucc_lt : k0.succ < kA.castSucc := by
        apply Fin.lt_def.mpr
        rw [Fin.val_succ, Fin.val_castSucc]
        omega
      have hult : u < L.t kA.castSucc := lt_of_le_of_lt hu1 (hstrict hsucc_lt)
      have harc : L.arcLen u (L.t kA.castSucc) < L.M := by
        have hgj : L.gidx (L.t kA.castSucc) = kA := L.gidx_t_castSucc hstrict kA
        show (L.gidx (L.t kA.castSucc) : ℕ) - (L.gidx u : ℕ)
            + (if L.t kA.castSucc = L.t (L.gidx (L.t kA.castSucc)).castSucc then 0 else 1) < L.M
        rw [hgj, if_pos rfl, hkAv]
        omega
      have hwrap : L.wrapM u (L.t kA.castSucc) = 2 := by
        have hgj : L.gidx (L.t kA.castSucc) = kA := L.gidx_t_castSucc hstrict kA
        have hnc : L.wrapNC u = 0 :=
          L.wrapNC_eq_zero_of_le_vertex_one hstrict hM2 (by rw [← hk0succ]; exact hu1)
        show 2 + L.wrapNB (L.t kA.castSucc) + L.wrapNC u = 2
        unfold PolyLoop.wrapNB
        rw [hgj, hkAv, hnc]
        omega
      exact L.no_double_point_of_lt hL hmin hstrict hult huval' harc (by rw [hwrap]; omega)
    · rw [← hsec] at hAlt
      obtain ⟨u, hu0, hu1, huval⟩ := L.exists_eq_of_mem_segment kA hAlt
      have huval' : L.loop (L.t k0.succ) = L.loop u := Subtype.ext huval.symm
      have hlt : L.t k0.succ < u := by
        refine lt_of_lt_of_le ?_ hu0
        exact hstrict (by
          apply Fin.lt_def.mpr
          rw [Fin.val_succ, Fin.val_castSucc]
          omega)
      have hgu : L.gidx u = kA := by
        rcases eq_or_lt_of_le hu1 with hc | hc
        · rw [hc, hkAsucc, L.gidx_one, hkA]
        · exact L.gidx_eq_of_lt hu0 hc
      have hg1 : L.gidx (L.t k0.succ) = ⟨1, by omega⟩ := by
        have h1 : k0.succ = (⟨1, by omega⟩ : Fin L.M).castSucc := by
          apply Fin.ext
          rw [hk0]
          simp
        rw [h1, L.gidx_t_castSucc hstrict]
      have harc : L.arcLen (L.t k0.succ) u < L.M := by
        show (L.gidx u : ℕ) - (L.gidx (L.t k0.succ) : ℕ)
            + (if u = L.t (L.gidx u).castSucc then 0 else 1) < L.M
        rw [hgu, hg1, hkAv]
        simp only [Fin.val_mk]
        split <;> omega
      have hwrap : L.wrapM (L.t k0.succ) u = 2 := by
        have hnc : L.wrapNC (L.t k0.succ) = 0 := by
          have h1 : k0.succ = (⟨1, by omega⟩ : Fin L.M).castSucc := rfl
          rw [h1, L.wrapNC_castSucc hstrict (⟨1, by omega⟩ : Fin L.M)]
          simp
        show 2 + L.wrapNB u + L.wrapNC (L.t k0.succ) = 2
        unfold PolyLoop.wrapNB
        rw [hgu, hkAv, hnc]
        omega
      exact L.no_double_point_of_lt hL hmin hstrict hlt huval' harc (by rw [hwrap]; omega)

/-- The index of the time `0` is `0`. -/
lemma PolyLoop.gidx_zero (L : PolyLoop Ω) (hstrict : StrictMono L.t) :
    L.gidx (0 : I) = ⟨0, L.hM⟩ := by
  rw [← L.ht0]
  exact L.gidx_t_castSucc hstrict ⟨0, L.hM⟩

/-- The `wrapNC` value at the time `0`. -/
lemma PolyLoop.wrapNC_zero (L : PolyLoop Ω) (hstrict : StrictMono L.t) :
    L.wrapNC (0 : I) = 0 := by
  have h0 : L.t (⟨0, L.hM⟩ : Fin L.M).castSucc = (0 : I) := by
    have h1 : (⟨0, L.hM⟩ : Fin L.M).castSucc = (0 : Fin (L.M+1)) := by
      apply Fin.ext
      simp
    rw [h1, L.ht0]
  rw [← h0, L.wrapNC_castSucc hstrict ⟨0, L.hM⟩]
  simp

/-- **Wrap case of the double-point analysis.**  If the complementary arc is at least as long as
the whole loop, we reach a contradiction. -/
theorem PolyLoop.wrap_case (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) (hstrict : StrictMono L.t)
    (hM3 : 3 ≤ L.M) (hnodeg : ∀ k : Fin L.M, L.loop (L.t k.castSucc) ≠ L.loop (L.t k.succ))
    {a b : I} (hab : a < b) (hval : L.loop a = L.loop b) (hE2 : L.M ≤ L.wrapM a b) : False := by
  have hE2' : L.M ≤ 2 + (L.M - 1 - (L.gidx b : ℕ)) + L.wrapNC a := hE2
  have hgb_le : (L.gidx b : ℕ) ≤ L.M - 1 := by have := (L.gidx b).2; omega
  have hNC : L.wrapNC a ≤ (L.gidx a : ℕ) := L.wrapNC_le a
  have hj_le : (L.gidx b : ℕ) ≤ (L.gidx a : ℕ) + 1 := by omega
  have hi_le_hj : (L.gidx a : ℕ) ≤ (L.gidx b : ℕ) := L.gidx_mono hab.le
  by_cases hji : L.gidx a = L.gidx b
  · exact absurd (L.eq_of_same_edge hji (hnodeg (L.gidx a)) hval) (ne_of_lt hab)
  · have hjb : (L.gidx b : ℕ) = (L.gidx a : ℕ) + 1 := by
      have h1 : (L.gidx a : ℕ) < (L.gidx b : ℕ) := Fin.lt_def.mp (lt_of_le_of_ne hi_le_hj hji)
      omega
    by_cases hdb : b = L.t (L.gidx b).castSucc
    · refine absurd ?_ (ne_of_lt hab)
      have hbeq : b = L.t (L.gidx a).succ := by
        rw [hdb]
        congr 1
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      have hb0 : L.t (L.gidx a).castSucc ≤ b := by
        rw [hbeq]
        exact L.htmono (Fin.castSucc_le_succ _)
      exact L.eq_of_loop_eq_on_edge (hnodeg (L.gidx a)) (L.gidx_le a) (le_gidx_succ L a) hb0
        (le_of_eq hbeq) hval
    · have hh : L.t (L.gidx b).castSucc = L.t (L.gidx a).succ := by
        congr 1
        apply Fin.ext
        simp only [Fin.val_castSucc, Fin.val_succ]
        omega
      have hXB : ((L.loop b : ↥Ω) : ℂ) ≠ (((L.loop (L.t (L.gidx a).succ) : ↥Ω)) : ℂ) := by
        intro hc
        have hc' : ((L.loop a : ↥Ω) : ℂ) = (((L.loop (L.t (L.gidx a).succ) : ↥Ω)) : ℂ) := by
          rw [hval]
          exact hc
        have haS : a = L.t (L.gidx a).succ := by
          by_cases hlt : a < L.t (L.gidx a).succ
          · exact absurd (L.eq_of_loop_eq_on_edge (hnodeg (L.gidx a)) (L.gidx_le a)
              (le_gidx_succ L a) (L.htmono (Fin.castSucc_le_succ _)) (le_refl _) (Subtype.ext hc'))
              (ne_of_lt hlt)
          · exact le_antisymm (le_gidx_succ L a) (not_lt.mp hlt)
        have hbS : b = L.t (L.gidx b).castSucc := by
          have h1 : L.loop b = L.loop (L.t (L.gidx b).castSucc) := by
            rw [← hval, haS, ← hh]
          exact L.eq_of_loop_eq_on_edge (hnodeg (L.gidx b)) (L.gidx_le b) (le_gidx_succ L b)
            (le_refl _) (L.htmono (Fin.castSucc_le_succ _)) h1
        exact hdb hbS
      have hmemA : ((L.loop b : ↥Ω) : ℂ) ∈ segment ℝ (((L.loop (L.t (L.gidx a).castSucc) : ↥Ω)) : ℂ)
          (((L.loop (L.t (L.gidx a).succ) : ↥Ω)) : ℂ) := by
        have h := L.mem_segment_of_edge (L.gidx a) (L.gidx_le a) (le_gidx_succ L a)
        rw [hval] at h
        exact h
      have hmemB : ((L.loop b : ↥Ω) : ℂ) ∈ segment ℝ (((L.loop (L.t (L.gidx a).succ) : ↥Ω)) : ℂ)
          (((L.loop (L.t (L.gidx b).succ) : ↥Ω)) : ℂ) := by
        have h := L.mem_segment_of_edge (L.gidx b) (L.gidx_le b) (le_gidx_succ L b)
        rw [show (((L.loop (L.t (L.gidx b).castSucc) : ↥Ω)) : ℂ)
            = (((L.loop (L.t (L.gidx a).succ) : ↥Ω)) : ℂ) from
          congrArg (fun z : I => ((L.loop z : ↥Ω) : ℂ)) hh] at h
        exact h
      rcases collinear_trichotomy hXB hmemA hmemB with hAlt | hAlt
      · -- the vertex `A` lies on the second edge
        rw [show (((L.loop (L.t (L.gidx a).succ) : ↥Ω)) : ℂ)
            = (((L.loop (L.t (L.gidx b).castSucc) : ↥Ω)) : ℂ) from
          (congrArg (fun z : I => ((L.loop z : ↥Ω) : ℂ)) hh).symm] at hAlt
        obtain ⟨u, hu0, hu1, huval⟩ := L.exists_eq_of_mem_segment (L.gidx b) hAlt
        have huval' : L.loop (L.t (L.gidx a).castSucc) = L.loop u := Subtype.ext huval.symm
        have hult : L.t (L.gidx a).castSucc < u := by
          have hclt : (L.gidx a).castSucc < (L.gidx a).succ := by
            apply Fin.lt_def.mpr
            simp only [Fin.val_castSucc, Fin.val_succ]
            omega
          have hlt' : L.t (L.gidx a).castSucc < L.t (L.gidx b).castSucc := by
            rw [hh]
            exact hstrict hclt
          exact lt_of_lt_of_le hlt' hu0
        have harc : L.arcLen (L.t (L.gidx a).castSucc) u < L.M := by
          have h1 : L.arcLen (L.t (L.gidx a).castSucc) (L.t (L.gidx a).succ) = 1 :=
            L.arcLen_castSucc_succ hstrict (L.gidx a)
          have h2 : L.arcLen (L.t (L.gidx a).succ) u ≤ 1 := by
            rw [← hh]
            exact L.arcLen_le_one_left hstrict hu0 hu1
          have h3 := L.arcLen_add_le (a := L.t (L.gidx a).castSucc) (b := L.t (L.gidx a).succ)
            (c := u) (L.htmono (Fin.castSucc_le_succ _)) (by rw [← hh]; exact hu0)
          omega
        have hgu_ge : (L.gidx a : ℕ) + 1 ≤ (L.gidx u : ℕ) := by
          have h1 : L.gidx (L.t (L.gidx b).castSucc) ≤ L.gidx u := L.gidx_mono hu0
          rw [L.gidx_t_castSucc hstrict] at h1
          have h2 : (L.gidx b : ℕ) ≤ (L.gidx u : ℕ) := Fin.le_iff_val_le_val.mp h1
          omega
        by_cases hia0 : (L.gidx a : ℕ) = 0
        · by_cases hgu2 : 2 ≤ (L.gidx u : ℕ)
          · have hwrap : L.wrapM (L.t (L.gidx a).castSucc) u < L.M := by
              have hNC0 : L.wrapNC (L.t (L.gidx a).castSucc) = 0 := by
                rw [L.wrapNC_castSucc hstrict (L.gidx a)]
                omega
              show 2 + L.wrapNB u + L.wrapNC (L.t (L.gidx a).castSucc) < L.M
              unfold PolyLoop.wrapNB
              rw [hNC0]
              have hul : (L.gidx u : ℕ) ≤ L.M - 1 := by have := (L.gidx u).2; omega
              omega
            exact L.no_double_point_of_lt hL hmin hstrict hult huval' harc hwrap
          · have hgu1 : (L.gidx u : ℕ) = 1 := by omega
            have hbaseu' : L.loop (L.t (L.gidx a).castSucc) = L.base := by
              have h0 : (L.gidx a).castSucc = (0 : Fin (L.M+1)) := by
                apply Fin.ext
                exact hia0
              rw [h0, L.ht0]
              exact L.loop.source'
            have hbaseu : ((L.loop (L.t (L.gidx a).castSucc) : ↥Ω) : ℂ)
                = ((L.base : ↥Ω) : ℂ) := congrArg (fun z : ↥Ω => (z : ℂ)) hbaseu'
            have hval2 : L.loop u = L.loop (1 : I) := by
              have h1 : L.loop u = L.loop (L.t (L.gidx a).castSucc) := Subtype.ext huval
              rw [h1, hbaseu']
              exact L.loop.target'.symm
            have hult1 : u < (1 : I) := by
              have h1 : (L.gidx b).succ < Fin.last L.M := by
                apply Fin.lt_def.mpr
                simp only [Fin.val_succ, Fin.val_last]
                omega
              have h2 : L.t (L.gidx b).succ < (1 : I) := by
                have h3 := hstrict h1
                rwa [L.ht1] at h3
              exact lt_of_le_of_lt hu1 h2
            have harc2 : L.arcLen u (1 : I) < L.M := by
              have hgu : L.gidx u = (⟨1, by omega⟩ : Fin L.M) := Fin.ext hgu1
              show (L.gidx (1 : I) : ℕ) - (L.gidx u : ℕ)
                  + (if (1 : I) = L.t (L.gidx (1 : I)).castSucc then 0 else 1) < L.M
              rw [L.gidx_one, hgu]
              have hif : ¬ ((1 : I) = L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc) := by
                intro hc
                have h4 : L.t (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc < (1 : I) := by
                  have h5 := hstrict (show (⟨L.M - 1, by have := L.hM; omega⟩ : Fin L.M).castSucc
                      < Fin.last L.M from by
                    apply Fin.lt_def.mpr
                    simp only [Fin.val_castSucc, Fin.val_last, Fin.val_mk]
                    omega)
                  rwa [L.ht1] at h5
                exact absurd hc.symm (ne_of_lt h4)
              rw [if_neg hif]
              simp only [Fin.val_mk]
              omega
            have hNCu : L.wrapNC u = 1 := by
              have hgu : L.gidx u = (⟨1, by omega⟩ : Fin L.M) := Fin.ext hgu1
              have hune : u ≠ L.t (⟨1, by omega⟩ : Fin L.M).castSucc := by
                intro hc
                have hB : ((L.loop (L.t (L.gidx a).succ) : ↥Ω) : ℂ)
                    = ((L.loop (L.t (⟨1, by omega⟩ : Fin L.M).castSucc) : ↥Ω) : ℂ) := by
                  have hidx : (L.gidx a).succ = (⟨1, by omega⟩ : Fin L.M).castSucc := by
                    apply Fin.ext
                    simp only [Fin.val_succ, Fin.val_castSucc]
                    omega
                  rw [hidx]
                have h1 : L.loop (L.t (L.gidx a).castSucc) = L.loop (L.t (L.gidx a).succ) := by
                  apply Subtype.ext
                  rw [← huval, hc, hB]
                exact hnodeg (L.gidx a) h1
              unfold PolyLoop.wrapNC
              rw [hgu]
              rw [if_neg (by simp : ¬ ((⟨1, by omega⟩ : Fin L.M) : ℕ) = 0)]
              rw [if_neg hune]
              simp
            have hwrap2 : L.wrapM u (1 : I) ≤ 3 := by
              have hgj : L.gidx (1 : I) = ⟨L.M - 1, by have := L.hM; omega⟩ := L.gidx_one
              show 2 + L.wrapNB (1 : I) + L.wrapNC u ≤ 3
              unfold PolyLoop.wrapNB
              rw [hgj, hNCu]
              simp only [Fin.val_mk]
              omega
            by_cases hM4 : 4 ≤ L.M
            · have hlt2 : L.wrapM u (1 : I) < L.M := by
                have h34 : (3 : ℕ) < L.M := by omega
                exact lt_of_le_of_lt hwrap2 h34
              exact L.no_double_point_of_lt hL hmin hstrict hult1 hval2 harc2 hlt2
            · have h3 : L.M = 3 := by omega
              have hgb1 : L.gidx b = (⟨1, by omega⟩ : Fin L.M) := by
                apply Fin.ext
                simp only [Fin.val_mk]
                omega
              have hseg := L.mem_segment_of_edge (L.gidx b) hu0 hu1
              rw [huval, hbaseu] at hseg
              rw [hgb1] at hseg
              exact hL (L.homotopic_refl_of_M_eq_three h3 hseg)
        · have hwrap : L.wrapM (L.t (L.gidx a).castSucc) u < L.M := by
            have hNCa : L.wrapNC (L.t (L.gidx a).castSucc) = (L.gidx a : ℕ) - 1 :=
              L.wrapNC_castSucc hstrict (L.gidx a)
            show 2 + L.wrapNB u + L.wrapNC (L.t (L.gidx a).castSucc) < L.M
            unfold PolyLoop.wrapNB
            rw [hNCa]
            have hul : (L.gidx u : ℕ) ≤ L.M - 1 := by have := (L.gidx u).2; omega
            omega
          exact L.no_double_point_of_lt hL hmin hstrict hult huval' harc hwrap
      · -- the vertex `C` lies on the first edge
        obtain ⟨u, hu0, hu1, huval⟩ := L.exists_eq_of_mem_segment (L.gidx a) hAlt
        have huval' : L.loop u = L.loop (L.t (L.gidx b).succ) := Subtype.ext huval
        have hult : u < L.t (L.gidx b).succ := by
          have hclt : (L.gidx b).castSucc < (L.gidx b).succ := by
            apply Fin.lt_def.mpr
            simp only [Fin.val_castSucc, Fin.val_succ]
            omega
          have hlt' : L.t (L.gidx b).castSucc < L.t (L.gidx b).succ := hstrict hclt
          rw [hh] at hlt'
          exact lt_of_le_of_lt hu1 hlt'
        have harc : L.arcLen u (L.t (L.gidx b).succ) < L.M := by
          have h1 : L.arcLen u (L.t (L.gidx b).castSucc) ≤ 1 := by
            rw [hh]
            exact L.arcLen_le_one_right hstrict hu0 hu1
          have h2 : L.arcLen (L.t (L.gidx b).castSucc) (L.t (L.gidx b).succ) = 1 :=
            L.arcLen_castSucc_succ hstrict (L.gidx b)
          have h3 := L.arcLen_add_le (a := u) (b := L.t (L.gidx b).castSucc)
            (c := L.t (L.gidx b).succ) (by rw [hh]; exact hu1)
            (L.htmono (Fin.castSucc_le_succ _))
          omega
        have hgu_le : (L.gidx u : ℕ) ≤ (L.gidx b : ℕ) := by
          have h1 : L.gidx u ≤ L.gidx (L.t (L.gidx b).castSucc) :=
            L.gidx_mono (by rw [hh]; exact hu1)
          rw [L.gidx_t_castSucc hstrict] at h1
          exact Fin.le_iff_val_le_val.mp h1
        have hgu_ge : (L.gidx a : ℕ) ≤ (L.gidx u : ℕ) := by
          have h1 : L.gidx (L.t (L.gidx a).castSucc) ≤ L.gidx u := L.gidx_mono hu0
          rw [L.gidx_t_castSucc hstrict] at h1
          exact Fin.le_iff_val_le_val.mp h1
        have hNC_lt : L.wrapNC u < (L.gidx b : ℕ) := by
          by_cases heq : (L.gidx u : ℕ) = (L.gidx b : ℕ)
          · have hufin : L.gidx u = L.gidx b := Fin.ext heq
            have hu_eq : u = L.t (L.gidx b).castSucc :=
              L.eq_castSucc_of_gidx_eq hufin (le_trans hu1 (le_of_eq hh.symm))
            rw [hu_eq, L.wrapNC_castSucc hstrict (L.gidx b)]
            omega
          · have hlt : (L.gidx u : ℕ) < (L.gidx b : ℕ) := lt_of_le_of_ne hgu_le heq
            have h4 := L.wrapNC_le u
            omega
        by_cases hb1 : (L.gidx b : ℕ) + 1 < L.M
        · have hgj : L.gidx (L.t (L.gidx b).succ) = (⟨(L.gidx b : ℕ) + 1, hb1⟩ : Fin L.M) :=
            L.gidx_t_succ hstrict (L.gidx b) hb1
          have hwrap : L.wrapM u (L.t (L.gidx b).succ) < L.M := by
            show 2 + L.wrapNB (L.t (L.gidx b).succ) + L.wrapNC u < L.M
            unfold PolyLoop.wrapNB
            rw [hgj]
            simp only [Fin.val_mk]
            omega
          exact L.no_double_point_of_lt hL hmin hstrict hult huval' harc hwrap
        · have hbe : (L.gidx b : ℕ) = L.M - 1 := by omega
          have hCbase : (((L.loop (L.t (L.gidx b).succ) : ↥Ω)) : ℂ) = ((L.base : ↥Ω) : ℂ) := by
            have h2 : (L.gidx b).succ = Fin.last L.M := by
              apply Fin.ext
              simp only [Fin.val_succ, Fin.val_last]
              omega
            rw [h2, L.ht1]
            exact congrArg (fun z : ↥Ω => (z : ℂ)) L.loop.target'
          by_cases hug : (L.gidx u : ℕ) = (L.gidx b : ℕ)
          · have hufin : L.gidx u = L.gidx b := Fin.ext hug
            have hu_eq : u = L.t (L.gidx b).castSucc :=
              L.eq_castSucc_of_gidx_eq hufin (le_trans hu1 (le_of_eq hh.symm))
            have hcontra : L.loop (L.t (L.gidx b).castSucc) = L.loop (L.t (L.gidx b).succ) := by
              apply Subtype.ext
              rw [← hu_eq]
              exact huval
            exact hnodeg (L.gidx b) hcontra
          · have hgua : (L.gidx u : ℕ) = (L.gidx a : ℕ) := by omega
            have h0u : ((L.loop (0 : I) : ↥Ω) : ℂ) = ((L.loop u : ↥Ω) : ℂ) := by
              rw [huval, hCbase]
              exact congrArg (fun z : ↥Ω => (z : ℂ)) L.loop.source'
            have h0ult : (0 : I) < u := by
              have h2 : (0 : I) < L.t (L.gidx a).castSucc := by
                rw [← L.ht0]
                apply hstrict
                apply Fin.lt_def.mpr
                simp only [Fin.val_castSucc, Fin.val_zero]
                omega
              exact lt_of_lt_of_le h2 hu0
            have harc3 : L.arcLen (0 : I) u < L.M := by
              have hgj0 : L.gidx (0 : I) = ⟨0, L.hM⟩ := L.gidx_zero hstrict
              have hgu : (L.gidx u : ℕ) = L.M - 2 := by omega
              show (L.gidx u : ℕ) - (L.gidx (0 : I) : ℕ)
                  + (if u = L.t (L.gidx u).castSucc then 0 else 1) < L.M
              rw [hgj0, hgu]
              simp only [Fin.val_mk]
              split <;> omega
            have hwrap3 : L.wrapM (0 : I) u ≤ 3 := by
              have hNC0 : L.wrapNC (0 : I) = 0 := L.wrapNC_zero hstrict
              have hgu : (L.gidx u : ℕ) = L.M - 2 := by omega
              show 2 + L.wrapNB u + L.wrapNC (0 : I) ≤ 3
              unfold PolyLoop.wrapNB
              rw [hNC0, hgu]
              omega
            by_cases hM4 : 4 ≤ L.M
            · have hlt3 : L.wrapM (0 : I) u < L.M := by
                have h34 : (3 : ℕ) < L.M := by omega
                exact lt_of_le_of_lt hwrap3 h34
              exact L.no_double_point_of_lt hL hmin hstrict h0ult (Subtype.ext h0u) harc3 hlt3
            · have h3 : L.M = 3 := by omega
              have hga1 : L.gidx a = (⟨1, by omega⟩ : Fin L.M) := by
                apply Fin.ext
                simp only [Fin.val_mk]
                omega
              have hseg := L.mem_segment_of_edge (L.gidx a) hu0 hu1
              rw [huval, hCbase] at hseg
              rw [hga1] at hseg
              exact hL (L.homotopic_refl_of_M_eq_three h3 hseg)

/-- **The double-point analysis for a minimal essential polygonal loop.**  The only double point
of a minimal essential polygonal loop is the trivial one `(0, 1)`. -/
theorem PolyLoop.eq_zero_one_of_double_point (L : PolyLoop Ω) (hL : L.Essential)
    (hmin : ∀ L' : PolyLoop Ω, L'.Essential → L.M ≤ L'.M) (hstrict : StrictMono L.t)
    (hM3 : 3 ≤ L.M) (hnodeg : ∀ k : Fin L.M, L.loop (L.t k.castSucc) ≠ L.loop (L.t k.succ))
    {a b : I} (hab : a < b) (hval : L.loop a = L.loop b) : a = 0 ∧ b = 1 := by
  by_cases hE1 : L.M ≤ L.arcLen a b
  · exact L.forward_case hL hmin hstrict hM3 hnodeg hab hval hE1
  · by_cases hE2 : L.M ≤ L.wrapM a b
    · exact (L.wrap_case hL hmin hstrict hM3 hnodeg hab hval hE2).elim
    · exact (L.no_double_point_of_lt hL hmin hstrict hab hval (not_le.mp hE1)
        (not_le.mp hE2)).elim

/-- **The cutting lemma.**  In an open subset `Ω ⊆ ℂ`, every loop that is not null-homotopic
contains an essential *embedded* circle. -/
theorem exists_injective_circle_of_essential_loop {Ω : Set ℂ} (hΩ : IsOpen Ω) {x : ↥Ω}
    (p : Path x x) (hp : ¬ p.Homotopic (Path.refl x)) :
    ∃ J : C(Circle, ↥Ω), Function.Injective J ∧ ¬ J.Nullhomotopic := by
  classical
  obtain ⟨L₀, hL₀⟩ := exists_essential_polyLoop hΩ p hp
  have hex : ∃ n, ∃ L : PolyLoop Ω, L.Essential ∧ L.M = n := ⟨L₀.M, L₀, hL₀, rfl⟩
  obtain ⟨Lmin, hLmin_ess, hLmin_M⟩ := Nat.find_spec hex
  have hmin : ∀ L : PolyLoop Ω, L.Essential → Lmin.M ≤ L.M := fun L hL => by
    rw [hLmin_M]
    exact Nat.find_min' hex ⟨L, hL, rfl⟩
  have hstrict : StrictMono Lmin.t := Lmin.strictMono_of_isMin hLmin_ess hmin
  have hM3 : 3 ≤ Lmin.M := Lmin.three_le_of_isMin hLmin_ess hmin
  have hnodeg := Lmin.no_degenerate_of_isMin hLmin_ess hmin hstrict hM3
  have hinj : Set.InjOn Lmin.loop (Set.Ico (0 : Set.Icc (0:ℝ) 1) 1) := by
    intro s hs t ht hst
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h01 := Lmin.eq_zero_one_of_double_point hLmin_ess hmin hstrict hM3 hnodeg hlt hst
      exact absurd h01.2 (ne_of_lt ht.2)
    · have h01 := Lmin.eq_zero_one_of_double_point hLmin_ess hmin hstrict hM3 hnodeg hgt hst.symm
      exact absurd h01.2 (ne_of_lt hs.2)
  exact ⟨Lmin.toCircle, Lmin.toCircle_injective hinj, Lmin.not_nullhomotopic_toCircle hLmin_ess⟩


end

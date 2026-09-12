import Mathlib
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_mem_intrinsicInterior_exposedFace
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_smear_dissection
import Submission.Commons.Geometry.Convex.Hadwiger.polytope_parallelBody_cellDecomposition

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set
open scoped Pointwise BigOperators Convex Topology

namespace Commons.Geometry.Convex.Hadwiger

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V]

/-- if `a` is constantly `c` on `s`, it is constantly `c` on the affine span of `s` -/
lemma sef_inner_const_on_affineSpan {a : V} {s : Set V} {c : ℝ}
    (h : ∀ x ∈ s, inner ℝ a x = c) : ∀ x ∈ affineSpan ℝ s, inner ℝ a x = c := by
  intro x hx
  refine affineSpan_induction (k := ℝ) (V := V) (P := V)
    (p := fun z => inner ℝ a z = c) hx ?_ ?_
  · intro y hy
    exact h y hy
  · intro r u v w hu hv hw
    calc
      inner ℝ a (r • (u -ᵥ v) +ᵥ w) = inner ℝ a (r • (u - v) + w) := by rfl
      _ = r * inner ℝ a (u - v) + inner ℝ a w := by
        rw [inner_add_right, inner_smul_right]
      _ = r * (inner ℝ a u - inner ℝ a v) + inner ℝ a w := by
        rw [inner_sub_right]
      _ = r * (c - c) + c := by rw [hu, hv, hw]
      _ = c := by ring

/-- membership of a difference in the direction of the affine span -/
lemma sef_vsub_mem_direction_of_mem_span {A : Set V} {a b : V}
    (ha : a ∈ affineSpan ℝ A) (hb : b ∈ affineSpan ℝ A) :
    a - b ∈ (affineSpan ℝ A).direction := by
  rw [← vsub_eq_sub]
  exact AffineSubspace.vsub_mem_direction (s := affineSpan ℝ A) ha hb

/-- A nonempty exposed face of the convex hull of `u` contains a generator. -/
lemma sef_exists_mem_generator_of_isExposed (u : Finset V) (P : Set V)
    (hP : P = convexHull ℝ (u : Set V)) {H : Set V}
    (hH : IsExposed ℝ P H) (hHne : H.Nonempty) : ∃ t0 : V, t0 ∈ H ∧ t0 ∈ u := by
  classical
  have hconv : H = convexHull ℝ (H ∩ (u : Set V)) :=
    exposedFace_conv_vertices_generic u P hP hH hHne
  have hne' : (H ∩ (u : Set V)).Nonempty := by
    have : (convexHull ℝ (H ∩ (u : Set V))).Nonempty := by
      rwa [← hconv]
    exact (convexHull_nonempty_iff (𝕜 := ℝ) (s := H ∩ (u : Set V))).mp this
  rcases hne' with ⟨t0, ht0⟩
  exact ⟨t0, ht0.1, ht0.2⟩

/-- exposed nonempty proper face is the top face in a nonzero direction -/
lemma sef_exposed_face_eq_topFace_of_ne {P : Set V} {H : Set V}
    (hH : IsExposed ℝ P H) (hHne : H.Nonempty) (hHproper : H ≠ P) :
    ∃ a : V, a ≠ 0 ∧ H = topFace a P := by
  classical
  rcases hH hHne with ⟨l, hl⟩
  let a : V := (InnerProductSpace.toDual ℝ V).symm l
  have hin : ∀ z : V, inner ℝ a z = l z := by
    intro z
    exact (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := V) (x := z) (y := l))
  have hset : H = topFace a P := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ {x' : V | x' ∈ P ∧ ∀ y ∈ P, l y ≤ l x'} := by
        rw [hl] at hx
        exact hx
      refine ⟨hx'.1, ?_⟩
      intro y hy
      have hy1 : l y ≤ l x := hx'.2 y hy
      simpa [hin] using hy1
    · intro hx
      have hxP : x ∈ P := (topFace_subset (n := a) (P := P)) hx
      have hxmax : ∀ y ∈ P, inner ℝ a y ≤ inner ℝ a x := hx.2
      rw [hl]
      exact ⟨hxP, fun y hy => by simpa [hin] using hxmax y hy⟩
  refine ⟨a, ?_, hset⟩
  intro ha0
  apply hHproper
  rw [hset]
  have htop0 : topFace (0 : V) P = P := by
    ext x
    constructor
    · intro hx
      exact (topFace_subset (n := 0) (P := P)) hx
    · intro hxP
      exact mem_topFace_of_forall_le hxP (fun y hy => by simp)
  simpa [ha0] using htop0

/-- vertices of the top face have `a`-value equal to the top value; others strictly below -/
lemma sef_inner_le_of_topFace {a t0 : V} {P : Set V} (ht0 : t0 ∈ topFace a P) :
    ∀ t ∈ P, inner ℝ a t ≤ inner ℝ a t0 := by
  intro t ht
  exact topFace_le_of_mem (n := a) ht0 ht

/-- vertices lie in the polytope -/
lemma sef_mem_of_mem_vertex {u : Finset V} {P : Set V} (hP : P = convexHull ℝ (u : Set V))
    {t : V} (ht : t ∈ u) : t ∈ P := by
  rw [hP]
  exact subset_convexHull ℝ (u : Set V) ht

/-- if the affine span of the vertices is everything, the span of the vertex differences is
everything -/
lemma sef_span_vsub_eq_top_of_affineSpan_eq_top {u : Finset V} {t0 : V} (ht0 : t0 ∈ u)
    (hspan : affineSpan ℝ (u : Set V) = ⊤) :
    Submodule.span ℝ ((fun x : V => x - t0) '' (u : Set V)) = ⊤ := by
  have hdir : (affineSpan ℝ (u : Set V)).direction = (⊤ : AffineSubspace ℝ V).direction := by
    rw [hspan]
  have hdir' : (affineSpan ℝ (u : Set V)).direction = ⊤ := by
    simpa using hdir
  have hvspan : vectorSpan ℝ (u : Set V) = ⊤ := by
    simpa [direction_affineSpan] using hdir'
  have hvsub : vectorSpan ℝ (u : Set V) =
      Submodule.span ℝ ((fun x : V => x -ᵥ t0) '' (u : Set V)) :=
    vectorSpan_eq_span_vsub_set_right (k := ℝ) (V := V) (P := V)
      (s := (u : Set V)) (p := t0) ht0
  rw [hvsub] at hvspan
  simpa [vsub_eq_sub] using hvspan

/-- a vector orthogonal to every vertex difference is zero (when vertices affinely span) -/
lemma sef_eq_zero_of_inner_vsub_eq_zero {u : Finset V} {t0 : V} (ht0 : t0 ∈ u)
    (hspan : Submodule.span ℝ ((fun x : V => x - t0) '' (u : Set V)) = ⊤)
    {u0 : V} (h : ∀ t ∈ u, inner ℝ u0 (t - t0) = 0) : u0 = 0 := by
  classical
  let B : Set V := (fun x : V => x - t0) '' (u : Set V)
  have hspanB : Submodule.span ℝ B = ⊤ := hspan
  have hu0orth : u0 ∈ (Submodule.span ℝ B)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro z hz
    refine Submodule.span_induction (s := B) (p := fun x _ => inner ℝ u0 x = 0) ?_ ?_ ?_ ?_ hz
    · intro y hyB
      rcases hyB with ⟨t, ht, rfl⟩
      exact h t ht
    · simp
    · intro x y hx hy hx0 hy0
      rw [inner_add_right]
      simp [hx0, hy0]
    · intro r x hx hx0
      rw [inner_smul_right]
      simp [hx0]
  have hu0top : u0 ∈ (⊤ : Submodule ℝ V)ᗮ := by
    rwa [← hspanB]
  rw [Submodule.top_orthogonal_eq_bot] at hu0top
  exact (Submodule.mem_bot ℝ).mp hu0top

/-- the exposing direction is orthogonal to the direction of the affine span of the face -/
lemma sef_mem_orthogonal_direction_of_topFace {P H : Set V} {a t0 : V}
    (hHtop : H = topFace a P) (ht0H : t0 ∈ H) :
    a ∈ ((affineSpan ℝ (H : Set V)).direction)ᗮ := by
  classical
  rw [Submodule.mem_orthogonal']
  intro d hd
  let c : ℝ := inner ℝ a t0
  have hconst : ∀ x ∈ affineSpan ℝ (H : Set V), inner ℝ a x = c := by
    refine sef_inner_const_on_affineSpan (s := H) (c := c) ?_
    intro x hxH
    have hxF : x ∈ topFace a P := by simpa [hHtop] using hxH
    have ht0F : t0 ∈ topFace a P := by simpa [hHtop] using ht0H
    dsimp [c]
    exact topFace_eq_of_mem (n := a) hxF ht0F
  have hne : ((affineSpan ℝ (H : Set V) : AffineSubspace ℝ V) : Set V).Nonempty := by
    exact ⟨t0, subset_affineSpan ℝ (H : Set V) ht0H⟩
  rcases (AffineSubspace.mem_direction_iff_eq_vsub (k := ℝ) (V := V) (P := V)
      (s := affineSpan ℝ (H : Set V)) hne d).mp hd with ⟨p₁, hp₁, p₂, hp₂, hdEq⟩
  have hp1c : inner ℝ a p₁ = c := hconst p₁ hp₁
  have hp2c : inner ℝ a p₂ = c := hconst p₂ hp₂
  have hdEq' : d = p₁ - p₂ := by simpa [vsub_eq_sub] using hdEq
  rw [hdEq', inner_sub_right]
  rw [hp1c, hp2c]
  ring

/-- a nonzero vector in `Dᗮ` perpendicular to `a`, when `D` has codimension at least two -/
lemma sef_exists_perp_direction_of_codim_ge_two {D : Submodule ℝ V} {a : V}
    (haD : a ∈ Dᗮ) (ha0 : a ≠ 0)
    (hdim : Module.finrank ℝ D + 1 < Module.finrank ℝ V) :
    ∃ u : V, u ≠ 0 ∧ u ∈ Dᗮ ∧ inner ℝ u a = 0 := by
  classical
  let S : Submodule ℝ V := ℝ ∙ a
  have haS : a ∈ S := by
    exact (Submodule.mem_span_singleton (R := ℝ) (M := V)).mpr ⟨1, by simp⟩
  have hSle : S ≤ Dᗮ := by
    intro x hx
    rcases (Submodule.mem_span_singleton (R := ℝ) (M := V)).mp (by simpa [S] using hx) with ⟨c, hc⟩
    rw [← hc]
    exact (Dᗮ).smul_mem c haD
  have hfD : Module.finrank ℝ D + Module.finrank ℝ (Dᗮ : Submodule ℝ V) =
      Module.finrank ℝ V := Submodule.finrank_add_finrank_orthogonal D
  have hf2 : 2 ≤ Module.finrank ℝ (Dᗮ : Submodule ℝ V) := by
    have h1 : Module.finrank ℝ D + 1 < Module.finrank ℝ V := hdim
    omega
  have hneq : Dᗮ ≠ S := by
    intro hEq
    have hf1 : Module.finrank ℝ (Dᗮ : Submodule ℝ V) = 1 := by
      rw [hEq]
      exact finrank_span_singleton (K := ℝ) ha0
    omega
  have hnot_le : ¬ Dᗮ ≤ S := by
    intro hle
    exact hneq (le_antisymm hle hSle)
  have hu0 : ∃ u0 : V, u0 ∈ Dᗮ ∧ u0 ∉ S := by
    by_contra hc
    apply hnot_le
    intro u0 hu0D
    by_contra hu0S
    exact hc ⟨u0, hu0D, hu0S⟩
  rcases hu0 with ⟨u0, hu0D, hu0S⟩
  let κ : ℝ := inner ℝ u0 a / inner ℝ a a
  let u : V := u0 - κ • a
  have huD : u ∈ Dᗮ := by
    dsimp [u]
    exact (Dᗮ).sub_mem hu0D ((Dᗮ).smul_mem κ haD)
  have hun : u ≠ 0 := by
    intro hu0
    apply hu0S
    apply (Submodule.mem_span_singleton (R := ℝ) (M := V)).mpr
    refine ⟨κ, ?_⟩
    have hz : u0 - κ • a = 0 := by simpa [u] using hu0
    exact (sub_eq_zero.mp hz).symm
  have hua : inner ℝ u a = 0 := by
    have haa : inner ℝ a a ≠ 0 := (inner_self_ne_zero (𝕜 := ℝ) (x := a)).mpr ha0
    have hκ : (inner ℝ u0 a / inner ℝ a a) * inner ℝ a a = inner ℝ u0 a := by
      exact div_mul_cancel₀ (inner ℝ u0 a) haa
    dsimp [u, κ]
    calc
      inner ℝ (u0 - (inner ℝ u0 a / inner ℝ a a) • a) a
          = inner ℝ u0 a - inner ℝ ((inner ℝ u0 a / inner ℝ a a) • a) a := by rw [inner_sub_left]
      _ = inner ℝ u0 a - (inner ℝ u0 a / inner ℝ a a) * inner ℝ a a := by
          rw [inner_smul_left]
          simp
      _ = 0 := by rw [hκ]; ring
  exact ⟨u, hun, huD, hua⟩

/-- choose sign of a nonzero perpendicular direction so that some vertex has strictly positive
component -/
lemma sef_exists_vertex_strict_direction {u : Finset V} {t0 : V} (ht0 : t0 ∈ u)
    (hspan : Submodule.span ℝ ((fun x : V => x - t0) '' (u : Set V)) = ⊤)
    {D : Submodule ℝ V} {a u0 : V}
    (hu0D : u0 ∈ Dᗮ) (hu0a : inner ℝ u0 a = 0) (hu0ne : u0 ≠ 0) :
    ∃ w : V, w ≠ 0 ∧ w ∈ Dᗮ ∧ inner ℝ w a = 0 ∧ ∃ t ∈ u, 0 < inner ℝ w (t - t0) := by
  classical
  by_cases hpos : ∃ t ∈ u, 0 < inner ℝ u0 (t - t0)
  · rcases hpos with ⟨t₁, ht₁u, ht₁pos⟩
    exact ⟨u0, hu0ne, hu0D, hu0a, t₁, ht₁u, ht₁pos⟩
  · have hneq : ∃ t ∈ u, inner ℝ u0 (t - t0) ≠ 0 := by
      by_contra hc
      apply hu0ne
      apply sef_eq_zero_of_inner_vsub_eq_zero (u := u) (u0 := u0) ht0 hspan
      intro t ht
      by_contra hz
      exact hc ⟨t, ht, hz⟩
    rcases hneq with ⟨t₁, ht₁u, ht₁ne⟩
    refine ⟨-u0, ?_, ?_, ?_, t₁, ht₁u, ?_⟩
    · intro h
      exact hu0ne (neg_eq_zero.mp h)
    · exact (Dᗮ).neg_mem hu0D
    · simp [hu0a]
    · have hle : inner ℝ u0 (t₁ - t0) ≤ 0 := le_of_not_gt (fun h => hpos ⟨t₁, ht₁u, h⟩)
      have hlt : inner ℝ u0 (t₁ - t0) < 0 := lt_of_le_of_ne hle ht₁ne
      simpa using (neg_pos.mpr hlt)

/-- linearity of the inner product over a weighted sum of vectors -/
lemma sef_inner_sum_smul_sub {ι : Type*} (s : Finset ι) (w : ι → ℝ) (m : V) (p : ι → V)
    (z : V) : inner ℝ m (∑ i ∈ s, w i • (p i - z)) =
      ∑ i ∈ s, w i * inner ℝ m (p i - z) := by
  classical
  let g : V →ₗ[ℝ] ℝ := (InnerProductSpace.toDual ℝ V m).toLinearMap
  have hg : ∀ y : V, g y = inner ℝ m y := by
    intro y
    exact (InnerProductSpace.toDual_apply_apply (𝕜 := ℝ) (E := V) (x := m) (y := y))
  calc
    inner ℝ m (∑ i ∈ s, w i • (p i - z)) = g (∑ i ∈ s, w i • (p i - z)) := by simp [hg]
    _ = ∑ i ∈ s, w i * inner ℝ m (p i - z) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [map_smul]
      simp [hg]

/-- a linear functional nonpositive on the vertices is nonpositive on the whole polytope -/
lemma sef_inner_sub_le_of_vertex_le {u : Finset V} {P : Set V} (hP : P = convexHull ℝ (u : Set V))
    {m t0 : V} (hm : ∀ t ∈ u, inner ℝ m (t - t0) ≤ 0) :
    ∀ x ∈ P, inner ℝ m (x - t0) ≤ 0 := by
  intro x hx
  rw [hP] at hx
  rcases (Finset.mem_convexHull' (s := u) (x := x)).1 hx with ⟨w, hw0, hw1, hwx⟩
  have hxsub : x - t0 = ∑ t ∈ u, w t • (t - t0) := by
    calc
      x - t0 = (∑ t ∈ u, w t • t) - (∑ t ∈ u, w t) • t0 := by
        rw [hwx, hw1]
        simp
      _ = (∑ t ∈ u, w t • t) - (∑ t ∈ u, w t • t0) := by
        rw [Finset.sum_smul]
      _ = ∑ t ∈ u, (w t • t - w t • t0) := by rw [Finset.sum_sub_distrib]
      _ = ∑ t ∈ u, w t • (t - t0) := by
        refine Finset.sum_congr rfl ?_
        intro t ht
        rw [smul_sub]
  calc
    inner ℝ m (x - t0) = inner ℝ m (∑ t ∈ u, w t • (t - t0)) := by rw [hxsub]
    _ = ∑ t ∈ u, w t * inner ℝ m (t - t0) := sef_inner_sum_smul_sub u w m (fun t : V => t) t0
    _ ≤ 0 := by
      exact Finset.sum_nonpos (fun t ht => mul_nonpos_of_nonneg_of_nonpos (hw0 t ht) (hm t ht))

/-- elements of the orthogonal complement of a direction annihilate differences in that direction -/
lemma sef_inner_eq_of_mem_orthogonal_direction {D : Submodule ℝ V} {m : V} (hmD : m ∈ Dᗮ) {x y : V}
    (hD : x - y ∈ D) : inner ℝ m x = inner ℝ m y := by
  have hz : inner ℝ m (x - y) = 0 := by
    rw [Submodule.mem_orthogonal'] at hmD
    exact hmD (x - y) hD
  rw [inner_sub_right] at hz
  linarith

end

theorem exposed_face_strict_extension {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V] [FiniteDimensional ℝ V]
    (u : Finset V) (P : Set V) (hP : P = convexHull ℝ (u : Set V))
    (hint : (interior P).Nonempty) {H : Set V}
    (hHexp : IsExposed ℝ P H) (hHne : H.Nonempty) (hHproper : H ≠ P)
    (hdim : Module.finrank ℝ (affineSpan ℝ (H : Set V)).direction + 1 < Module.finrank ℝ V) :
    ∃ G : Set V, G.Nonempty ∧ IsExposed ℝ P G ∧ G ≠ P ∧ H ⊂ G := by
  classical
  rcases sef_exposed_face_eq_topFace_of_ne (P := P) (H := H) hHexp hHne hHproper with ⟨a, ha0, hHa⟩
  rcases sef_exists_mem_generator_of_isExposed u P hP hHexp hHne with ⟨t0, ht0H, ht0u⟩
  have ht0F : t0 ∈ topFace a P := by simpa [hHa] using ht0H
  have hPcvx : Convex ℝ P := by
    rw [hP]
    exact convex_convexHull ℝ (u : Set V)
  have hPaff : affineSpan ℝ (P : Set V) = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hPcvx).mp hint
  have huaff : affineSpan ℝ (u : Set V) = ⊤ := by
    calc
      affineSpan ℝ (u : Set V) = affineSpan ℝ (convexHull ℝ (u : Set V)) :=
        (affineSpan_convexHull (𝕜 := ℝ) (E := V) (s := (u : Set V))).symm
      _ = affineSpan ℝ (P : Set V) := by rw [hP]
      _ = ⊤ := hPaff
  let D : Submodule ℝ V := (affineSpan ℝ (H : Set V)).direction
  have haD : a ∈ Dᗮ := by
    exact sef_mem_orthogonal_direction_of_topFace (P := P) (H := H) (a := a) (t0 := t0) hHa ht0H
  have hspan : Submodule.span ℝ ((fun x : V => x - t0) '' (u : Set V)) = ⊤ :=
    sef_span_vsub_eq_top_of_affineSpan_eq_top (u := u) (t0 := t0) ht0u huaff
  rcases sef_exists_perp_direction_of_codim_ge_two (D := D) (a := a) haD ha0 hdim with
    ⟨u0, hu0ne, hu0D, hu0a⟩
  rcases sef_exists_vertex_strict_direction (u := u) (t0 := t0) ht0u hspan (D := D) (a := a)
      (u0 := u0) hu0D hu0a hu0ne with ⟨n, hnn, hnD, hna, hnpos⟩
  let bad : Finset V := u.filter (fun t : V => 0 < inner ℝ n (t - t0))
  have hbad : bad.Nonempty := by
    rcases hnpos with ⟨t, ht, hpos⟩
    refine ⟨t, ?_⟩
    simpa [bad] using ⟨ht, hpos⟩
  let rat : V → ℝ := fun t => -(inner ℝ a (t - t0)) / inner ℝ n (t - t0)
  let S : Finset ℝ := bad.image rat
  have hSne : S.Nonempty := Finset.image_nonempty.mpr hbad
  let lam : ℝ := S.min' hSne
  let m : V := a + lam • n
  -- every element of S is positive
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨t, ht, rfl⟩
    have ht_mem : t ∈ u := (Finset.mem_filter.mp ht).1
    have hposn : 0 < inner ℝ n (t - t0) := (Finset.mem_filter.mp ht).2
    have ht_not_H : t ∉ H := by
      intro htH
      have hv : t - t0 ∈ D := sef_vsub_mem_direction_of_mem_span (A := H) (a := t) (b := t0)
        (subset_affineSpan ℝ (H : Set V) htH) (subset_affineSpan ℝ (H : Set V) ht0H)
      have hz : inner ℝ n (t - t0) = 0 := by
        rw [Submodule.mem_orthogonal'] at hnD
        exact hnD (t - t0) hv
      linarith
    have hnega : inner ℝ a (t - t0) < 0 := by
      have htF : t ∉ topFace a P := by simpa [hHa] using ht_not_H
      have hlt := lt_inner_of_not_mem_topFace (n := a) (q := t0) (x := t) ht0F
        (sef_mem_of_mem_vertex hP ht_mem) htF
      rw [inner_sub_right]
      linarith
    exact div_pos (neg_pos.mpr hnega) hposn
  have hlam_mem : lam ∈ S := Finset.min'_mem S hSne
  have hlam_pos : 0 < lam := hSpos lam hlam_mem
  have hlam_le : ∀ t ∈ bad, lam ≤ rat t := by
    intro t ht
    have hratS : rat t ∈ S := Finset.mem_image.mpr ⟨t, ht, rfl⟩
    exact Finset.min'_le S (rat t) hratS
  have htight : ∃ tstar ∈ bad, rat tstar = lam := by
    rcases Finset.mem_image.mp hlam_mem with ⟨tstar, htstar, htstar_rat⟩
    exact ⟨tstar, htstar, htstar_rat⟩
  have hm_vertex : ∀ t ∈ u, inner ℝ m (t - t0) ≤ 0 := by
    intro t ht
    by_cases htbad : t ∈ bad
    · have hposn : 0 < inner ℝ n (t - t0) := (Finset.mem_filter.mp htbad).2
      have hden_ne : inner ℝ n (t - t0) ≠ 0 := ne_of_gt hposn
      have hlamle : lam ≤ -(inner ℝ a (t - t0)) / inner ℝ n (t - t0) := by
        simpa [rat] using hlam_le t htbad
      have hmult := mul_le_mul_of_nonneg_right hlamle (le_of_lt hposn)
      have hdiv : (-(inner ℝ a (t - t0)) / inner ℝ n (t - t0)) * inner ℝ n (t - t0) =
          -(inner ℝ a (t - t0)) := div_mul_cancel₀ (-(inner ℝ a (t - t0))) hden_ne
      have hlin : lam * inner ℝ n (t - t0) ≤ -(inner ℝ a (t - t0)) := by
        rwa [hdiv] at hmult
      have hsum : inner ℝ a (t - t0) + lam * inner ℝ n (t - t0) ≤ 0 := by
        linarith
      dsimp [m]
      rw [inner_add_left, inner_smul_left]
      simp
      exact hsum
    · have hgt : ¬ 0 < inner ℝ n (t - t0) := by
        intro hpos
        exact htbad (by simpa [bad] using ⟨ht, hpos⟩)
      have hnonpos : inner ℝ n (t - t0) ≤ 0 := le_of_not_gt hgt
      have hanonpos : inner ℝ a (t - t0) ≤ 0 := by
        have hle := sef_inner_le_of_topFace (a := a) (t0 := t0) ht0F t (sef_mem_of_mem_vertex hP ht)
        rw [inner_sub_right]
        linarith
      have hsum : inner ℝ a (t - t0) + lam * inner ℝ n (t - t0) ≤ 0 := by
        have h1 : lam * inner ℝ n (t - t0) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlam_pos) hnonpos
        linarith
      dsimp [m]
      rw [inner_add_left, inner_smul_left]
      simp
      exact hsum
  have hm_P : ∀ x ∈ P, inner ℝ m (x - t0) ≤ 0 := sef_inner_sub_le_of_vertex_le hP hm_vertex
  have hmD : m ∈ Dᗮ := by
    dsimp [m]
    exact (Dᗮ).add_mem haD ((Dᗮ).smul_mem lam hnD)
  have hH_const : ∀ h ∈ H, inner ℝ m h = inner ℝ m t0 := by
    intro h hhH
    have hv : h - t0 ∈ D := sef_vsub_mem_direction_of_mem_span (A := H) (a := h) (b := t0)
      (subset_affineSpan ℝ (H : Set V) hhH) (subset_affineSpan ℝ (H : Set V) ht0H)
    exact sef_inner_eq_of_mem_orthogonal_direction (D := D) (m := m) hmD hv
  have ht0P : t0 ∈ P := sef_mem_of_mem_vertex hP ht0u
  have ht0G : t0 ∈ topFace m P := by
    refine mem_topFace_of_forall_le ht0P ?_
    intro y hy
    have hy' : inner ℝ m (y - t0) ≤ 0 := hm_P y hy
    rw [inner_sub_right] at hy'
    linarith
  have hHG : H ⊆ topFace m P := by
    intro h hhH
    have hhP : h ∈ P := (IsExposed.subset hHexp) hhH
    refine mem_topFace_of_forall_le hhP ?_
    intro y hy
    have hy' : inner ℝ m (y - t0) ≤ 0 := hm_P y hy
    have hconst : inner ℝ m t0 = inner ℝ m h := (hH_const h hhH).symm
    rw [inner_sub_right] at hy'
    rw [← hconst]
    linarith
  rcases htight with ⟨tstar, htstarbad, htight_rat⟩
  have htstaru : tstar ∈ u := (Finset.mem_filter.mp htstarbad).1
  have htstarpos : 0 < inner ℝ n (tstar - t0) := (Finset.mem_filter.mp htstarbad).2
  have htstarnotH : tstar ∉ H := by
    intro htstarH
    have hv : tstar - t0 ∈ D := sef_vsub_mem_direction_of_mem_span (A := H) (a := tstar) (b := t0)
      (subset_affineSpan ℝ (H : Set V) htstarH) (subset_affineSpan ℝ (H : Set V) ht0H)
    have hz : inner ℝ n (tstar - t0) = 0 := by
      rw [Submodule.mem_orthogonal'] at hnD
      exact hnD (tstar - t0) hv
    linarith
  have hm_tstar : inner ℝ m (tstar - t0) = 0 := by
    have hden_ne : inner ℝ n (tstar - t0) ≠ 0 := ne_of_gt htstarpos
    have ht_rat : -(inner ℝ a (tstar - t0)) / inner ℝ n (tstar - t0) = lam := by
      simpa [rat] using htight_rat
    have hc := congrArg (fun x : ℝ => x * inner ℝ n (tstar - t0)) ht_rat
    have hlin : -(inner ℝ a (tstar - t0)) = lam * inner ℝ n (tstar - t0) := by
      rwa [div_mul_cancel₀ (-(inner ℝ a (tstar - t0))) hden_ne] at hc
    dsimp [m]
    rw [inner_add_left, inner_smul_left]
    simp
    calc
      inner ℝ a (tstar - t0) + lam * inner ℝ n (tstar - t0)
          = inner ℝ a (tstar - t0) + -(inner ℝ a (tstar - t0)) := by rw [← hlin]
      _ = 0 := by ring
  have htstarP : tstar ∈ P := sef_mem_of_mem_vertex hP htstaru
  have htstarG : tstar ∈ topFace m P := by
    refine mem_topFace_of_forall_le htstarP ?_
    intro y hy
    have hy' : inner ℝ m (y - t0) ≤ 0 := hm_P y hy
    have hconst : inner ℝ m t0 = inner ℝ m tstar := by
      have hz : inner ℝ m (tstar - t0) = 0 := hm_tstar
      rw [inner_sub_right] at hz
      linarith
    rw [inner_sub_right] at hy'
    rw [← hconst]
    linarith
  have hm_ne : m ≠ 0 := by
    intro hm0
    have hpos : 0 < inner ℝ m a := by
      have hmA : inner ℝ m a = inner ℝ a a := by
        dsimp [m]
        rw [inner_add_left, inner_smul_left]
        simp [hna]
      rw [hmA]
      have hnorm : 0 < ‖a‖ ^ 2 := by
        exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr ha0)
      rwa [real_inner_self_eq_norm_sq]
    have hz := congrArg (fun x : V => inner ℝ x a) hm0
    simp at hz
    linarith
  let G : Set V := topFace m P
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · exact ⟨t0, ht0G⟩
  · exact isExposed_topFace m P
  · simpa [G] using topFace_ne_P_of_ne_zero (P := P) hint hm_ne
  · constructor
    · simpa [G] using hHG
    · intro hGleH
      exact htstarnotH (hGleH htstarG)

end Commons.Geometry.Convex.Hadwiger

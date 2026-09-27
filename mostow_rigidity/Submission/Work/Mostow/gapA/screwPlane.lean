import Mathlib
import Submission.Work.Mostow.gapA.screwDefs
import Submission.Work.Mostow.gapA.screwNorm
import Submission.Work.Mostow.gapA.screwTrig

/-!
# `screwPlane`: the rotation orbit meets every equal-norm vector

Let `a ≠ b` be distinct boundary points of `Sph 3` and let `Nsub a b` be the normal space of the
geodesic through them, a positive definite plane for the Minkowski form `minkN a b`.  Let
`R : Nsub a b ≃ₗ[ℝ] Nsub a b` be a form-preserving linear equivalence which is a rotation by
`±2π/M`, i.e. `minkN (R w) w = cos (2π/M) · minkN w w` for all `w`.

The theorem says: for any two vectors `u`, `w` of `Nsub a b` of equal length, some element
`R ^ j` (`j ∈ ℤ`) of the cyclic rotation group brings `u` to within angle `π/M` of `w`, i.e.

`cos (π/M) · minkN a b u u ≤ minkN a b w ((R ^ j) u)`.

The proof is a reduction to plane trigonometry:
* `orthJofQuad` produces the `90°`-rotation operator `J` with `J² = -1`, `B`-orthogonal and
  `B (J x) x = 0`, and `R = cos θ · 1 + sin θ · J`;
* `zpowCosSin` computes `R ^ j = cos (jθ) · 1 + sin (jθ) · J` for all `j : ℤ`;
* `decompOrthPair` decomposes `w` in the orthonormal pair `u`, `J u` with `a² + b² = 1`;
* `screwTrig` (proved separately) is the plane statement that the `M`-th roots of unity come
  within `π/M` of any point of the circle.
-/

namespace Work.Mostow.gapA

noncomputable section

/-! ## Bilinearity of a form `B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` -/

theorem Bilin_add_l {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y z : V) : B (x + y) z = B x z + B y z := by simp
theorem Bilin_add_r {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y z : V) : B x (y + z) = B x y + B x z := by simp
theorem Bilin_smul_l {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (a : ℝ) (x y : V) : B (a • x) y = a * B x y := by simp
theorem Bilin_smul_r {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (a : ℝ) (x y : V) : B x (a • y) = a * B x y := by simp
theorem Bilin_sub_l {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y z : V) : B (x - y) z = B x z - B y z := by simp
theorem Bilin_sub_r {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (x y z : V) : B x (y - z) = B x y - B x z := by simp

/-! ## Powers of a rotation -/

/-- If `J² = -1` and `R = cos θ · 1 + sin θ · J` then `R ^ j = cos (jθ) · 1 + sin (jθ) · J`
for every `j : ℤ`. -/
theorem zpowCosSin {V : Type*} [AddCommGroup V] [Module ℝ V]
    (R : V ≃ₗ[ℝ] V) (J : V →ₗ[ℝ] V) (θ : ℝ)
    (hJ : ∀ x : V, J (J x) = -x)
    (hR : ∀ x : V, R x = Real.cos θ • x + Real.sin θ • J x) :
    ∀ (j : ℤ) (x : V), (R ^ j) x = Real.cos ((j : ℝ) * θ) • x + Real.sin ((j : ℝ) * θ) • J x := by
  have hRs : ∀ y : V, R⁻¹ y = Real.cos θ • y - Real.sin θ • J y := by
    intro y
    have h1 : R (Real.cos θ • y - Real.sin θ • J y) = y := by
      rw [map_sub, map_smul, map_smul, hR y, hR (J y), hJ y]
      match_scalars <;> (try ring) <;> nlinarith [Real.cos_sq_add_sin_sq θ]
    have h2 : R⁻¹ y = R⁻¹ (R (Real.cos θ • y - Real.sin θ • J y)) := by rw [h1]
    rw [h2]
    exact LinearEquiv.symm_apply_apply R (Real.cos θ • y - Real.sin θ • J y)
  have hnat : ∀ k : ℕ, ∀ x : V,
      (R ^ k) x = Real.cos ((k:ℝ) * θ) • x + Real.sin ((k:ℝ) * θ) • J x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', LinearEquiv.mul_apply, ih x, map_add, map_smul, map_smul, hR x, hR (J x), hJ x]
      rw [show (((k+1:ℕ)):ℝ) * θ = (k:ℝ) * θ + θ by push_cast; ring, Real.cos_add, Real.sin_add]
      module
  have hsymm : ∀ k : ℕ, ∀ x : V,
      ((R⁻¹) ^ k) x = Real.cos ((k:ℝ) * θ) • x - Real.sin ((k:ℝ) * θ) • J x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', LinearEquiv.mul_apply, ih x, map_sub, map_smul, map_smul, hRs x, hRs (J x),
          hJ x]
      rw [show (((k+1:ℕ)):ℝ) * θ = (k:ℝ) * θ + θ by push_cast; ring, Real.cos_add, Real.sin_add]
      module
  intro j x
  by_cases hj : 0 ≤ j
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
    rw [hk, zpow_natCast, hnat k x]
    simp only [Int.cast_natCast]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = -((k:ℕ) : ℤ) := by
      refine ⟨(-j).toNat, ?_⟩
      have h1 : (0:ℤ) ≤ -j := by omega
      have h2 : (((-j).toNat : ℕ) : ℤ) = -j := Int.toNat_of_nonneg h1
      omega
    rw [hk]
    have h1 : R ^ (-((k:ℕ) : ℤ)) = (R⁻¹) ^ k := by rw [zpow_neg, zpow_natCast, ← inv_pow R k]
    rw [h1, hsymm k x]
    rw [show ((↑(-((k:ℕ) : ℤ)) : ℝ)) * θ = -((k:ℝ)*θ) by push_cast; ring, Real.cos_neg,
      Real.sin_neg, neg_smul, sub_eq_add_neg]

/-! ## The `90°`-rotation attached to a rotation by `θ` -/

/-- A form-preserving `R` with `B (R x) x = cos θ · B x x` (and `sin θ ≠ 0`) admits a
`B`-orthogonal complex structure `J` (`J² = -1`, `B (J x) x = 0`) with
`R = cos θ · 1 + sin θ · J`. -/
theorem orthJofQuad {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (_hdef : ∀ x, B x x = 0 → x = 0)
    (R : V ≃ₗ[ℝ] V) (hR : ∀ x y, B (R x) (R y) = B x y)
    (θ : ℝ) (hRq : ∀ x, B (R x) x = Real.cos θ * B x x) (hsin : Real.sin θ ≠ 0) :
    ∃ J : V →ₗ[ℝ] V, (∀ x, J (J x) = -x) ∧ (∀ x y, B (J x) (J y) = B x y) ∧
      (∀ x, B (J x) x = 0) ∧ (∀ x, R x = Real.cos θ • x + Real.sin θ • J x) := by
  let J0 : V →ₗ[ℝ] V := (Real.sin θ)⁻¹ • ((R : V →ₗ[ℝ] V) - Real.cos θ • 1)
  have hJ0 : ∀ x : V, J0 x = (Real.sin θ)⁻¹ • (R x - Real.cos θ • x) := by
    intro x
    rfl
  have hcs : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
    have h := Real.cos_sq_add_sin_sq θ; linarith
  have hzero : ∀ x : V, B (J0 x) x = 0 := by
    intro x
    rw [hJ0 x, Bilin_smul_l, Bilin_sub_l, Bilin_smul_l, hRq x]
    ring
  have hpolJ : ∀ u v : V, B (J0 u) v + B u (J0 v) = 0 := by
    intro u v
    have h0 := hzero (u + v)
    rw [show J0 (u + v) = J0 u + J0 v from LinearMap.map_add J0 u v] at h0
    simp only [Bilin_add_l, Bilin_add_r] at h0
    rw [hzero u, hzero v, hsym (J0 v) u] at h0
    linarith
  have hpolR : ∀ x y : V, B (R x) y + B (R y) x = 2 * Real.cos θ * B x y := by
    intro x y
    have h1 := hRq (x + y)
    rw [show R (x + y) = R x + R y from map_add R x y] at h1
    simp only [Bilin_add_l, Bilin_add_r] at h1
    rw [hRq x, hRq y, hsym y x] at h1
    linarith
  have horthJ : ∀ u v : V, B (J0 u) (J0 v) = B u v := by
    intro u v
    have h1 : B (R u - Real.cos θ • u) (R v - Real.cos θ • v)
        = B u v - Real.cos θ * (B (R u) v + B u (R v)) + Real.cos θ ^ 2 * B u v := by
      rw [Bilin_sub_l, Bilin_sub_r, Bilin_sub_r, Bilin_smul_l, Bilin_smul_r,
          Bilin_smul_l, Bilin_smul_r, hR u v]
      ring
    have h2 : B u (R v) = B (R v) u := hsym u (R v)
    rw [hJ0 u, hJ0 v, Bilin_smul_l, Bilin_smul_r, h1, h2, hpolR u v]
    rw [show B u v - Real.cos θ * (2 * Real.cos θ * B u v) + Real.cos θ ^ 2 * B u v
        = Real.sin θ ^ 2 * B u v by rw [hcs]; ring]
    rw [show (Real.sin θ)⁻¹ * ((Real.sin θ)⁻¹ * (Real.sin θ ^ 2 * B u v)) = B u v by
      rw [show (Real.sin θ)⁻¹ * ((Real.sin θ)⁻¹ * (Real.sin θ ^ 2 * B u v))
          = ((Real.sin θ)⁻¹ * Real.sin θ) * ((Real.sin θ)⁻¹ * Real.sin θ) * B u v by ring,
        inv_mul_cancel₀ hsin, one_mul, one_mul]]
  have hsq : ∀ x : V, J0 (J0 x) = -x := by
    intro x
    have key : ∀ y : V, B (J0 (J0 x)) y = - B x y := by
      intro y
      have h := hpolJ (J0 x) y
      rw [horthJ x y] at h
      linarith
    have hz : B (J0 (J0 x) + x) (J0 (J0 x) + x) = 0 := by
      rw [Bilin_add_l, Bilin_add_r, Bilin_add_r, key (J0 (J0 x)), key x,
          hsym x (J0 (J0 x)), key x]
      ring
    exact eq_neg_of_add_eq_zero_left (_hdef _ hz)
  refine ⟨J0, hsq, horthJ, hzero, ?_⟩
  intro x
  have h : Real.sin θ • J0 x = R x - Real.cos θ • x := by
    rw [hJ0 x, smul_smul, mul_inv_cancel₀ hsin, one_smul]
  rw [h]; abel

/-! ## Decomposition in an orthogonal pair -/

/-- In a two-dimensional space, a nonzero `B`-orthogonal pair `u`, `v` of equal `B`-length `n`
spans, so every `w` is a combination `w = a·u + b·v` with `B w u = a n`, `B w v = b n` and
`B w w = n (a² + b²)`. -/
theorem decompOrthPair {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (_hdef : ∀ x, B x x = 0 → x = 0)
    (hdim : Module.finrank ℝ V = 2)
    (u v : V) (n : ℝ) (hu : B u u = n) (hv : B v v = n) (huv : B u v = 0) (hn : n ≠ 0) :
    ∀ w : V, ∃ a b : ℝ, w = a • u + b • v ∧ B w u = a * n ∧ B w v = b * n
      ∧ B w w = n * (a ^ 2 + b ^ 2) := by
  have hu0 : u ≠ 0 := by
    intro h; apply hn; rw [← hu, h]; simp
  have hv0 : v ≠ 0 := by
    intro h; apply hn; rw [← hv, h]; simp
  have hli : LinearIndependent ℝ ![u, v] := by
    rw [linearIndependent_fin2]
    refine ⟨by simpa using hv0, ?_⟩
    intro a ha
    have ha' : a • v = u := by simpa using ha
    have h1 : a * n = 0 := by
      calc a * n = B (a • v) v := by rw [Bilin_smul_l, hv]
        _ = B u v := by rw [← ha']
        _ = 0 := huv
    rcases mul_eq_zero.mp h1 with h | h
    · rw [h, zero_smul] at ha'
      exact hu0 ha'.symm
    · exact hn h
  have hr : Set.range ![u, v] = ({u, v} : Set V) := by
    ext z; constructor
    · rintro ⟨i, rfl⟩; fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hspan : Submodule.span ℝ (Set.range ![u, v]) = ⊤ :=
    LinearIndependent.span_eq_top_of_card_eq_finrank hli (by rw [Fintype.card_fin, hdim])
  intro w
  have hw : w ∈ Submodule.span ℝ ({u, v} : Set V) := by
    rw [← hr, hspan]; trivial
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
  refine ⟨a, b, hab.symm, ?_, ?_, ?_⟩
  · rw [← hab]
    simp only [Bilin_add_l, Bilin_smul_l]
    rw [hu, hsym v u, huv]
    ring
  · rw [← hab]
    simp only [Bilin_add_l, Bilin_smul_l]
    rw [hv, huv]
    ring
  · rw [← hab]
    simp only [Bilin_add_l, Bilin_add_r, Bilin_smul_l, Bilin_smul_r]
    rw [hu, hv, hsym v u, huv]
    ring

/-! ## The abstract statement -/

/-- Abstract form of `screwPlane`: in a two-dimensional real space with a symmetric form `B`,
a `B`-orthogonal `R` with `B (R x) x = cos(2π/M) B x x` moves every vector `u` to within angle
`π/M` of any equal-length vector `w`. -/
theorem screwPlane_abstract {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x) (hdef : ∀ x, B x x = 0 → x = 0)
    (hdim : Module.finrank ℝ V = 2)
    (M : ℕ) (hM : 3 ≤ M)
    (R : V ≃ₗ[ℝ] V)
    (hR : ∀ x y, B (R x) (R y) = B x y)
    (hRq : ∀ x, B (R x) x = Real.cos (2 * Real.pi / M) * B x x)
    (u w : V) (hwn : B w w = B u u) :
    ∃ j : ℤ, Real.cos (Real.pi / M) * B u u ≤ B w ((R ^ j) u) := by
  by_cases hu : B u u = 0
  · have hu0 : u = 0 := hdef u hu
    refine ⟨0, ?_⟩
    rw [hu]
    simp [hu0]
  · have hMpos : 0 < M := by omega
    have hsin : Real.sin (2 * Real.pi / M) ≠ 0 := by
      apply (Real.sin_pos_of_pos_of_lt_pi ?_ ?_).ne'
      · positivity
      · rw [div_lt_iff₀ (by positivity : (0:ℝ) < M)]
        have hM3 : (3:ℝ) ≤ M := by exact_mod_cast hM
        nlinarith [Real.pi_pos]
    obtain ⟨J, hJsq, hJorth, hJzero, hRsplit⟩ :=
      orthJofQuad B hsym hdef R hR (2 * Real.pi / M) hRq hsin
    have hpow := zpowCosSin R J (2 * Real.pi / M) hJsq hRsplit
    obtain ⟨a, b, _hwab, hBwu, hBwJu, hBww⟩ :=
      decompOrthPair B hsym hdef hdim u (J u) (B u u) rfl (hJorth u u)
        (by rw [hsym u (J u), hJzero u]) hu w
    have hab2 : a ^ 2 + b ^ 2 = 1 := by
      have h1 : B u u * (a ^ 2 + b ^ 2) = B u u * 1 := by rw [mul_one, ← hBww, hwn]
      exact mul_left_cancel₀ hu h1
    obtain ⟨j, hj⟩ := screwTrig M hMpos a b hab2
    refine ⟨j, ?_⟩
    have hBuu_pos : 0 < B u u := lt_of_le_of_ne (hpos u) (Ne.symm hu)
    refine le_trans (mul_le_mul_of_nonneg_right hj (le_of_lt hBuu_pos)) ?_
    rw [hpow j u, Bilin_add_r, Bilin_smul_r, Bilin_smul_r, hBwu, hBwJu]
    rw [show (j:ℝ) * (2 * Real.pi / M) = 2 * Real.pi * (j:ℝ) / M by ring]
    apply le_of_eq; ring

/-! ## The target -/

/-- The linear functional `y ↦ minkN a b x y`. -/
def minkNN (a b : Submission.Mostow.E 3) (x : Nsub a b) : Nsub a b →ₗ[ℝ] ℝ where
  toFun y := minkN a b x y
  map_add' := by
    intro y₁ y₂
    simp only [minkN, Submodule.coe_add]
    rw [sn_mink_add_right]
  map_smul' := by
    intro r y
    simp only [minkN, Submodule.coe_smul]
    rw [sn_mink_smul_right, smul_eq_mul, RingHom.id_apply]

@[simp] lemma minkNN_apply (a b : Submission.Mostow.E 3) (x y : Nsub a b) :
    minkNN a b x y = minkN a b x y := rfl

/-- The Minkowski form on the normal space of the geodesic through `a` and `b`, as a bilinear
map. -/
def minkForm (a b : Submission.Mostow.E 3) : Nsub a b →ₗ[ℝ] Nsub a b →ₗ[ℝ] ℝ where
  toFun := minkNN a b
  map_add' := by
    intro x₁ x₂
    ext y
    simp only [minkNN_apply, LinearMap.add_apply, minkN, Submodule.coe_add]
    rw [sn_mink_add_left]
  map_smul' := by
    intro r x
    ext y
    simp only [minkNN_apply, LinearMap.smul_apply, minkN, Submodule.coe_smul]
    rw [sn_mink_smul_left, smul_eq_mul, RingHom.id_apply]

@[simp] lemma minkForm_apply (a b : Submission.Mostow.E 3) (x y : Nsub a b) :
    minkForm a b x y = minkN a b x y := rfl

/-- **`screwPlane`.** Some element of the cyclic rotation group generated by `R` brings `u`
within angle `π/M` of `w`. -/
theorem screwPlane {a b : Submission.Mostow.E 3} (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (hdim : Module.finrank ℝ (Work.Mostow.gapA.Nsub a b) = 2) (M : ℕ) (hM : 3 ≤ M)
    (R : Work.Mostow.gapA.Nsub a b ≃ₗ[ℝ] Work.Mostow.gapA.Nsub a b)
    (hRform : ∀ x y : Work.Mostow.gapA.Nsub a b, Work.Mostow.gapA.minkN a b (R x) (R y) = Work.Mostow.gapA.minkN a b x y)
    (hRquad : ∀ w : Work.Mostow.gapA.Nsub a b, Work.Mostow.gapA.minkN a b (R w) w = Real.cos (2 * Real.pi / M) * Work.Mostow.gapA.minkN a b w w)
    (u w : Work.Mostow.gapA.Nsub a b) (hwn : Work.Mostow.gapA.minkN a b w w = Work.Mostow.gapA.minkN a b u u) :
    ∃ j : ℤ, Real.cos (Real.pi / M) * Work.Mostow.gapA.minkN a b u u ≤ Work.Mostow.gapA.minkN a b w ((R ^ j) u) := by
  have key := screwPlane_abstract (minkForm a b)
    (by intro x y; simp only [minkForm_apply]; exact minkSeg_comm _ _)
    (by intro x; simp only [minkForm_apply]
        exact mink_nonneg_of_orth ha (x : Fin 3 ⊕ Fin 1 → ℝ) (mem_Nsub.mp x.2).1)
    (by intro x hx; simp only [minkForm_apply] at hx
        exact Subtype.ext (mink_eq_zero_of_orth ha hb hab (x : Fin 3 ⊕ Fin 1 → ℝ)
          (mem_Nsub.mp x.2).1 (mem_Nsub.mp x.2).2 hx))
    hdim M hM R
    (by intro x y; simp only [minkForm_apply]; exact hRform x y)
    (by intro x; simp only [minkForm_apply]; exact hRquad x)
    u w
    (by simp only [minkForm_apply]; exact hwn)
  simpa only [minkForm_apply] using key

end

end Work.Mostow.gapA

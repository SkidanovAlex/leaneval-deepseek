import Mathlib
open scoped Matrix
set_option autoImplicit false

noncomputable section

open unitInterval

/-!
# Lemma T, abstract topological core (Schwartz, "The optimal paper Moebius band")

A continuous odd unit-vector family `u : ℝ → S²` (`u (y+a) = −u y`) and a
continuous periodic midpoint family `m` (`m (y+a) = m y`) possess two points
`y` and `y+δ`, `0 < δ < a`, of the quotient centreline circle whose direction
vectors are perpendicular and whose midpoint displacement is coplanar with
them.

## Mathematical proof

For `x,δ ∈ ℝ` set `g(x,δ) = U x · U(x+δ)`, `h(x,δ) = (M x − M(x+δ)) ·
(U x × U(x+δ))` where `U y = u y` read on `Fin 3 → ℝ` and `M y = m y`.
Writing `Φ = (g,h)` (a continuous map `ℝ² → ℂ`), the identities
`u (x+a) = −u x`, `m (x+a) = m x`, `‖u x‖ = 1` give, *for every real
`x,δ`*:

* `Φ (x+δ) (a−δ) = −Φ x δ` (oddness w.r.t. the involution
  `Σ(x,δ)=(x+δ,a−δ)`),
* `Φ x 0 = 1` and `Φ x a = −1` (the two collapsed ends of the cylinder).

Suppose `Φ` had no zero on `0 < δ < a`.  On the square `I × I` (with
`s,t ∈ [0,1]`) define the normalized family
`P(s,t) = Φ(s·a·(1−t), a·t)/|…| ∈ S¹ ⊆ ℂ`.  Then `P₀ = P(0,·)` and
`P₁ = P(1,·)` are paths in the circle from `1` to `−1`, `P₀` and `P₁` are
homotopic relative to their endpoints (the straight-line interpolation in
`s`), and the oddness identity gives `P₁(t) = −P₀(σ t)` (`σ t = 1−t`).

Now lift the two paths through the universal covering
`exp : ℝ → S¹` (`IsCoveringMap Circle.exp`), with `P₀(0) = P₁(0) = exp 0`.
The covering-space homotopy-lifting property (`IsCoveringMap.liftPath`,
`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`,
`IsCoveringMap.eq_liftPath_iff'`) shows the two lifted paths share the same
endpoint.  The identity `P₁(t) = −P₀(σ t)` forces that common endpoint to
be `−x` where it is also `x`, hence `x = 0`; but the endpoint lifts a value
equal to `−1 = exp π ≠ 1 = exp 0`, contradiction.  This is the Borsuk–Ulam
principle `S² → ℝ²` in the explicit form needed here, applied to the
collapsed pair cylinder `(x mod a, δ)` ≅ `S²` on which `F = (g,h)` is the
odd map of the paper.
-/

namespace Commons.Topology.BorsukUlam

/-- The point `z / ‖z‖` of the unit circle (`Circle ⊆ ℂ`), for `z ≠ 0`. -/
def normCircle (z : ℂ) (hz : z ≠ 0) : Circle where
  val := z / ‖z‖
  property := mem_sphere_zero_iff_norm.2 <| by
    rw [norm_div]
    simp
    exact hz

@[simp]
lemma normCircle_val (z : ℂ) (hz : z ≠ 0) : (normCircle z hz : ℂ) = z / ‖z‖ := rfl

/-- `z ↦ z/‖z‖` is continuous on `ℂ \ {0}`. -/
lemma continuous_normCircle :
    Continuous (fun z : {w : ℂ // w ≠ 0} => normCircle z.1 z.2) := by
  apply Continuous.subtype_mk
  have hf : Continuous (fun z : {w : ℂ // w ≠ 0} => (z.1 : ℂ)) := continuous_subtype_val
  have hg : Continuous (fun z : {w : ℂ // w ≠ 0} => (‖z.1‖ : ℂ)) := by fun_prop
  refine Continuous.div₀ hf hg ?_
  intro z
  exact_mod_cast (norm_ne_zero_iff.mpr z.2)

/-- `normCircle` only depends on the value of its argument. -/
lemma normCircle_congr {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (h : z = w) :
    normCircle z hz = normCircle w hw := by
  apply Circle.ext
  rw [normCircle_val, normCircle_val]
  rw [h]

/-- `normCircle` commutes with negation: `normCircle (−z) = −normCircle z`. -/
lemma normCircle_neg (z : ℂ) (hz : z ≠ 0) (hzn : -z ≠ 0) : normCircle (-z) hzn = -normCircle z hz := by
  apply Circle.ext
  rw [normCircle_val]
  simp [normCircle_val]
  rw [neg_div]

@[simp]
lemma normCircle_one (hz : (1 : ℂ) ≠ 0) : normCircle (1 : ℂ) hz = 1 := by
  apply Circle.ext
  rw [normCircle_val]
  norm_num

@[simp]
lemma normCircle_neg_one (hz : (-1 : ℂ) ≠ 0) : normCircle (-1 : ℂ) hz = -1 := by
  apply Circle.ext
  rw [normCircle_val]
  norm_num

/-- Abstract Borsuk–Ulam content.  Two paths `P₀, P₁` in the circle, from `1`
to `−1`, homotopic relative to the endpoints, with `P₁ = −P₀ ∘ σ`, cannot
both avoid the origin, i.e. such data cannot exist.  (Equivalently: every
continuous odd map `S² → ℝ²` has a zero.) -/
lemma circle_reversal_contradiction (P₀ P₁ : C(I, Circle))
    (hHom : P₀.HomotopicRel P₁ ({0, 1} : Set I))
    (hP₀₀ : P₀ 0 = 1) (hP₀₁ : P₀ 1 = -1)
    (hRev : ∀ t : I, P₁ t = - P₀ (σ t)) : False := by
  let cov := Circle.isCoveringMap_exp
  have hP₁₀ : P₁ 0 = 1 := by
    have h := hRev (0 : I)
    rw [unitInterval.symm_zero] at h
    rw [hP₀₁] at h
    simpa using h
  have h₀ : P₀ 0 = Circle.exp 0 := by simpa [Circle.exp_zero] using hP₀₀
  have h₁ : P₁ 0 = Circle.exp 0 := by simpa [Circle.exp_zero] using hP₁₀
  let A₀ : C(I, ℝ) := cov.liftPath P₀ 0 h₀
  let A₁ : C(I, ℝ) := cov.liftPath P₁ 0 h₁
  have hA₀₁ : A₀ 1 = A₁ 1 := by
    exact cov.liftPath_apply_one_eq_of_homotopicRel hHom 0 h₀ h₁
  have hA₀lift : Circle.exp (A₀ 1) = -1 := by
    have hl := congr_fun (cov.liftPath_lifts P₀ 0 h₀) (1 : I)
    simpa [hP₀₁] using hl
  have hA₀liftAll : ∀ t : I, Circle.exp (A₀ t) = P₀ t :=
    fun t => congr_fun (cov.liftPath_lifts P₀ 0 h₀) t
  have hA₀₀ : A₀ 0 = 0 := cov.liftPath_zero P₀ 0 h₀
  let W : I → ℝ := fun t => A₀ (σ t) - A₀ 1
  have hWcont : Continuous W := by fun_prop
  have hWlift : ∀ t : I, Circle.exp (W t) = P₁ t := by
    intro t
    change Circle.exp (A₀ (σ t) - A₀ 1) = P₁ t
    rw [Circle.exp_sub]
    rw [hA₀liftAll (σ t), hA₀lift]
    rw [hRev t]
    simp [div_neg]
  have hW₀ : W 0 = 0 := by
    change A₀ (σ (0 : I)) - A₀ 1 = 0
    rw [unitInterval.symm_zero]
    ring
  have hEq : (⟨W, hWcont⟩ : C(I, ℝ)) = cov.liftPath P₁ 0 h₁ := by
    exact (cov.eq_liftPath_iff' (γ := P₁) (e := 0) (γ_0 := h₁)).mpr
      ⟨funext hWlift, hW₀⟩
  have hA₁eq : A₁ = (⟨W, hWcont⟩ : C(I, ℝ)) := hEq.symm
  have hA₁₁ : A₁ 1 = - A₀ 1 := by
    rw [hA₁eq]
    change W 1 = - A₀ 1
    change A₀ (σ (1 : I)) - A₀ 1 = - A₀ 1
    rw [unitInterval.symm_one]
    rw [hA₀₀]
    ring
  have hzero : A₀ 1 = 0 := by
    have h := hA₀₁.trans hA₁₁
    linarith
  have h1 : (1 : Circle) = -1 := by
    have hE : Circle.exp (A₀ 1) = Circle.exp 0 := congrArg Circle.exp hzero
    have h : Circle.exp 0 = -1 := hE.symm.trans hA₀lift
    simpa [Circle.exp_zero] using h
  exact (Circle.neg_ne_self (1 : Circle)).symm h1

/-- A continuous "complex family" `Φ : ℝ × ℝ → ℂ` with oddness
`Φ (x+δ) (a−δ) = −Φ x δ`, endpoint values `Φ x 0 = 1`, and no zeros on the
collapsed cylinder (`0 < a·t < a`), cannot exist.  The cylinder is viewed
through the square `(s,t) ↦ (s·a·(1−t), a·t)`. -/
lemma cylinder_odd_family_contradiction {a : ℝ} (_ha : 0 < a)
    (Φ : ℝ → ℝ → ℂ)
    (contΦ : Continuous (fun p : ℝ × ℝ => Φ p.1 p.2))
    (hPhi0 : ∀ x, Φ x 0 = 1) (hOdd : ∀ x δ, Φ (x + δ) (a - δ) = - Φ x δ)
    (hnz : ∀ s t : I, Φ ((s : ℝ) * a * (1 - (t : ℝ))) (a * (t : ℝ)) ≠ 0) : False := by
  have hPhia : ∀ x, Φ x a = -1 := by
    intro x
    have h := hOdd x 0
    have h' : Φ x a = -Φ x 0 := by simpa using h
    rw [hPhi0 x] at h'
    simpa using h'
  let zfun : I × I → ℂ := fun st => Φ ((st.1 : ℝ) * a * (1 - (st.2 : ℝ))) (a * (st.2 : ℝ))
  let Pf : I × I → Circle := fun st => normCircle (zfun st) (hnz st.1 st.2)
  have hzcont : Continuous zfun := by fun_prop
  have hPfcont : Continuous Pf := by
    dsimp [Pf]
    change Continuous (fun st : I × I =>
      normCircle ((⟨zfun st, hnz st.1 st.2⟩ : {w : ℂ // w ≠ 0}).1) (⟨zfun st, hnz st.1 st.2⟩ : {w : ℂ // w ≠ 0}).2)
    exact continuous_normCircle.comp (Continuous.subtype_mk hzcont (fun st => hnz st.1 st.2))
  let P0 : C(I, Circle) := ⟨fun t => Pf (0, t), hPfcont.comp (by fun_prop : Continuous fun t : I => ((0 : I), t))⟩
  let P1 : C(I, Circle) := ⟨fun t => Pf (1, t), hPfcont.comp (by fun_prop : Continuous fun t : I => ((1 : I), t))⟩
  have hz0 : ∀ s : I, zfun (s, 0) = 1 := by
    intro s; dsimp [zfun]; simp [hPhi0]
  have hz1 : ∀ s : I, zfun (s, 1) = -1 := by
    intro s; dsimp [zfun]; simp [hPhia]
  have hP₀₀ : P0 0 = 1 := by
    dsimp [P0, Pf]
    exact (normCircle_congr (z := zfun (0, 0)) (w := (1 : ℂ)) (hz := hnz (0 : I) (0 : I))
      (hw := by norm_num) (hz0 (0 : I))).trans (normCircle_one (by norm_num))
  have hP₀₁ : P0 1 = -1 := by
    dsimp [P0, Pf]
    exact (normCircle_congr (z := zfun (0, 1)) (w := (-1 : ℂ)) (hz := hnz (0 : I) (1 : I))
      (hw := by norm_num) (hz1 (0 : I))).trans (normCircle_neg_one (by norm_num))
  have hRev : ∀ t : I, P1 t = - P0 (σ t) := by
    intro t
    dsimp [P1, P0, Pf]
    have hodd0 : Φ (a * (1 - (t : ℝ))) (a * (t : ℝ)) = - Φ 0 (a * (1 - (t : ℝ))) := by
      have h := hOdd 0 (a * (1 - (t : ℝ)))
      have h1 : 0 + a * (1 - (t : ℝ)) = a * (1 - (t : ℝ)) := by ring
      have h2 : a - a * (1 - (t : ℝ)) = a * (t : ℝ) := by ring
      simpa [h1, h2] using h
    have hm : zfun (1, t) = - zfun (0, σ t) := by
      dsimp [zfun]
      have h1 : (1 : ℝ) * a * (1 - (t : ℝ)) = a * (1 - (t : ℝ)) := by ring
      have h2 : (0 : ℝ) * a * (1 - (1 - (t : ℝ))) = 0 := by ring
      rw [h1, h2]
      exact hodd0
    have hzzn : zfun (0, σ t) ≠ 0 := hnz (0 : I) (σ t)
    rw [normCircle_congr (z := zfun (1, t)) (w := - zfun (0, σ t))
        (hz := hnz (1 : I) t) (hw := neg_ne_zero.mpr hzzn) hm]
    rw [normCircle_neg (z := zfun (0, σ t)) (hz := hzzn)]
  have hP0P1 : P0.HomotopicRel P1 ({0,1} : Set I) := by
    refine ⟨?_⟩
    let Hcm : C(I × I, Circle) := ⟨Pf, hPfcont⟩
    let hHom0 : P0.Homotopy P1 :=
      { toContinuousMap := Hcm
        map_zero_left := by intro t; rfl
        map_one_left := by intro t; rfl }
    refine { toHomotopy := hHom0, prop' := ?_ }
    intro t x hx
    have hx01 : x = 0 ∨ x = 1 := by simpa using hx
    rcases hx01 with rfl | rfl
    · simp [hHom0, P0, Pf]
      exact normCircle_congr (z := zfun (t, 0)) (w := zfun (0, 0))
        (hz := hnz t (0 : I)) (hw := hnz (0 : I) (0 : I))
        ((hz0 t).trans (hz0 (0 : I)).symm)
    · simp [hHom0, P0, Pf]
      exact normCircle_congr (z := zfun (t, 1)) (w := zfun (0, 1))
        (hz := hnz t (1 : I)) (hw := hnz (0 : I) (1 : I))
        ((hz1 t).trans (hz1 (0 : I)).symm)
  exact circle_reversal_contradiction P0 P1 hP0P1 hP₀₀ hP₀₁ hRev

-- ============================================================
-- Analytic plumbing: continuity of dot and cross products on `Fin 3 → ℝ`.
-- ============================================================

/-- The dot product `(v,w) ↦ v·w` is continuous on `(Fin 3 → ℝ)²`. -/
lemma continuous_dot3 : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 ⬝ᵥ p.2) := by
  rw [show (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 ⬝ᵥ p.2) =
        fun p => ∑ i : Fin 3, p.1 i * p.2 i by
    funext p
    simp [dotProduct]]
  fun_prop

/-- The cross product `(v,w) ↦ v×w` is continuous on `(Fin 3 → ℝ)²`. -/
lemma continuous_cross3 : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => p.1 ⨯₃ p.2) := by
  apply continuous_pi
  intro j
  fin_cases j <;> simp [crossProduct] <;> fun_prop

/-- `‖u‖² = u·u` for vectors of the Euclidean space. -/
lemma self_dot_eq_norm_sq (x : EuclideanSpace ℝ (Fin 3)) : x.ofLp ⬝ᵥ x.ofLp = ‖x‖ ^ 2 := by
  rw [PiLp.norm_eq_of_L2]
  rw [Real.sq_sqrt]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Real.norm_eq_abs, sq_abs]
    ring
  · positivity

/-- `u·u = 1` when `u` is a unit vector. -/
lemma dot_self_of_unit {u : ℝ → EuclideanSpace ℝ (Fin 3)} (hu_unit : ∀ y, ‖u y‖ = 1)
    (y : ℝ) : (u y).ofLp ⬝ᵥ (u y).ofLp = 1 := by
  rw [self_dot_eq_norm_sq]
  rw [hu_unit y]
  norm_num

end Commons.Topology.BorsukUlam

namespace Commons.Topology.BorsukUlam

theorem exists_perp_coplanar_pair {a : ℝ} (ha : 0 < a)
    {u : ℝ → EuclideanSpace ℝ (Fin 3)} {m : ℝ → EuclideanSpace ℝ (Fin 3)}
    (hu_cont : Continuous u) (hu_unit : ∀ y, ‖u y‖ = 1)
    (hu_odd : ∀ y, u (y + a) = -u y)
    (hm_cont : Continuous m) (hm_per : ∀ y, m (y + a) = m y) :
    ∃ y : ℝ, ∃ δ : ℝ, 0 < δ ∧ δ < a ∧
      (WithLp.ofLp (u y) ⬝ᵥ WithLp.ofLp (u (y + δ)) = 0) ∧
      (WithLp.ofLp (m y - m (y + δ)) ⬝ᵥ
         (WithLp.ofLp (u y) ⨯₃ WithLp.ofLp (u (y + δ))) = 0) := by
  classical
  let U : ℝ → Fin 3 → ℝ := fun y => (u y).ofLp
  let M : ℝ → Fin 3 → ℝ := fun y => (m y).ofLp
  have hUodd : ∀ y, U (y + a) = - U y := by
    intro y
    dsimp [U]
    rw [hu_odd y]
    simp
  have hMper : ∀ y, M (y + a) = M y := by
    intro y
    dsimp [M]
    rw [hm_per y]
  have hUunit : ∀ y, U y ⬝ᵥ U y = 1 := by
    intro y
    dsimp [U]
    exact dot_self_of_unit hu_unit y
  have hU : Continuous U := by
    dsimp [U]
    apply continuous_pi
    intro i
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hu_cont
  have hM : Continuous M := by
    dsimp [M]
    apply continuous_pi
    intro i
    exact (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp hm_cont
  let g : ℝ → ℝ → ℝ := fun x δ => U x ⬝ᵥ U (x + δ)
  let h : ℝ → ℝ → ℝ := fun x δ => (M x - M (x + δ)) ⬝ᵥ (U x ⨯₃ U (x + δ))
  let Φ : ℝ → ℝ → ℂ := fun x δ => Complex.ofReal (g x δ) + Complex.I * Complex.ofReal (h x δ)
  have hgCont : Continuous (fun p : ℝ × ℝ => g p.1 p.2) := by
    dsimp [g]
    exact continuous_dot3.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => (U p.1, U (p.1 + p.2))))
  have hhCont : Continuous (fun p : ℝ × ℝ => h p.1 p.2) := by
    dsimp [h]
    exact continuous_dot3.comp (by fun_prop : Continuous (fun p : ℝ × ℝ => ((M p.1 - M (p.1 + p.2)), (U p.1 ⨯₃ U (p.1 + p.2)))))
  have hPhiCont : Continuous (fun p : ℝ × ℝ => Φ p.1 p.2) := by
    dsimp [Φ]
    fun_prop
  have hPhi0 : ∀ x, Φ x 0 = 1 := by
    intro x
    dsimp [Φ]
    have hg : g x 0 = 1 := by
      dsimp [g]
      simpa using hUunit x
    have hh : h x 0 = 0 := by
      dsimp [h]
      simp
    rw [hg, hh]
    norm_num
  have hOdd_g : ∀ x δ, g (x + δ) (a - δ) = - g x δ := by
    intro x δ
    dsimp [g]
    have h1 : (x + δ) + (a - δ) = x + a := by ring
    rw [h1]
    rw [hUodd x]
    rw [dotProduct_neg]
    congr 1
    exact dotProduct_comm (U (x + δ)) (U x)
  have hOdd_h : ∀ x δ, h (x + δ) (a - δ) = - h x δ := by
    intro x δ
    dsimp [h]
    have h1 : (x + δ) + (a - δ) = x + a := by ring
    rw [h1]
    rw [hUodd x, hMper x]
    have hc : U (x + δ) ⨯₃ (- U x) = - (U (x + δ) ⨯₃ U x) := by
      ext j
      fin_cases j <;> simp [crossProduct] <;> ring
    rw [hc]
    rw [dotProduct_neg]
    congr 1
    have hsub : M (x + δ) - M x = - (M x - M (x + δ)) := by ring
    rw [hsub]
    rw [neg_dotProduct]
    have ha := cross_anticomm (U x) (U (x + δ))
    rw [← ha]
    rw [dotProduct_neg]
    rw [neg_neg]
  have hOdd_Phi : ∀ x δ, Φ (x + δ) (a - δ) = - Φ x δ := by
    intro x δ
    dsimp [Φ]
    have hg := hOdd_g x δ
    have hh := hOdd_h x δ
    apply Complex.ext <;> simp [hg, hh]
  have hex : ∃ y δ, 0 < δ ∧ δ < a ∧ g y δ = 0 ∧ h y δ = 0 := by
    by_contra hnot
    have hno : ∀ x δ, 0 < δ → δ < a → ¬ (g x δ = 0 ∧ h x δ = 0) := by
      intro x δ hδ0 hδa hgh
      exact hnot ⟨x, δ, hδ0, hδa, hgh⟩
    have hPhi00_iff : ∀ x δ, Φ x δ = 0 ↔ g x δ = 0 ∧ h x δ = 0 := by
      intro x δ
      dsimp [Φ]
      constructor
      · intro hz
        have hr := congrArg Complex.re hz
        have hi := congrArg Complex.im hz
        constructor
        · simpa using hr
        · simpa using hi
      · rintro ⟨hg0, hh0⟩
        rw [hg0, hh0]
        simp
    have hnz : ∀ s t : I, Φ ((s : ℝ) * a * (1 - (t : ℝ))) (a * (t : ℝ)) ≠ 0 := by
      intro s t
      by_cases ht0 : (t : ℝ) = 0
      · have hz : a * (t : ℝ) = 0 := by rw [ht0]; ring
        have : Φ ((s : ℝ) * a * (1 - (t : ℝ))) (a * (t : ℝ)) ≠ 0 := by
          rw [hz, hPhi0]
          norm_num
        exact this
      · by_cases ht1 : (t : ℝ) = 1
        · have hz : a * (t : ℝ) = a := by rw [ht1]; ring
          have hPa : Φ ((s : ℝ) * a * (1 - (t : ℝ))) a = -1 := by
            have h := hOdd_Phi ((s : ℝ) * a * (1 - (t : ℝ))) 0
            simpa [hPhi0] using h
          have : Φ ((s : ℝ) * a * (1 - (t : ℝ))) (a * (t : ℝ)) ≠ 0 := by
            rw [hz, hPa]
            norm_num
          exact this
        · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne (unitInterval.nonneg t) (Ne.symm ht0)
          have htlt : (t : ℝ) < 1 := lt_of_le_of_ne (unitInterval.le_one t) ht1
          have hd0 : 0 < a * (t : ℝ) := mul_pos ha htpos
          have hda : a * (t : ℝ) < a := by nlinarith [ha, htlt]
          have hgh := hno ((s : ℝ) * a * (1 - (t : ℝ))) (a * (t : ℝ)) hd0 hda
          exact (hPhi00_iff ((s : ℝ) * a * (1 - (t : ℝ))) (a * (t : ℝ))).not.mpr hgh
    exact cylinder_odd_family_contradiction ha Φ hPhiCont hPhi0 hOdd_Phi hnz
  rcases hex with ⟨y, δ, hδ0, hδa, hgy, hhy⟩
  refine ⟨y, δ, hδ0, hδa, ?_, ?_⟩
  · dsimp [g, U] at hgy
    change (u y).ofLp ⬝ᵥ (u (y + δ)).ofLp = 0 at hgy
    simpa using hgy
  · dsimp [h, U, M] at hhy
    simpa [WithLp.ofLp_sub] using hhy

end Commons.Topology.BorsukUlam


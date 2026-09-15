import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_bound_m_strip

namespace Commons.NumberTheory.Zeta

open Complex MeasureTheory Filter
open scoped Topology

/-! ## Helper lemmas for the strip version of the Green–Tao contour lemma -/

/-- **Gluing a cutoff with a strip-continuous function.**  If `χ : X → ℝ` is continuous, `f : X → ℂ`
is continuous on an open set `U`, `χ` vanishes off `U`, and `f` is bounded by `B` on `U`, then the
product `χ • f` is continuous on all of `X`.  (Near a boundary point of `U` the factor `χ` tends to
`0`, while `f` stays bounded on the `U`-side.) -/
theorem continuous_ofReal_mul_of_continuousOn {X : Type*} [TopologicalSpace X]
    (χ : X → ℝ) (f : X → ℂ) (U : Set X) (B : ℝ)
    (hχ : Continuous χ) (hf : ContinuousOn f U) (hU : IsOpen U)
    (hzero : ∀ x, x ∉ U → χ x = 0) (hB : ∀ x ∈ U, ‖f x‖ ≤ B) :
    Continuous fun x => (χ x : ℂ) * f x := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : p ∈ U
  · have h1 : ContinuousAt (fun x : X => (χ x : ℂ)) p :=
      Complex.continuous_ofReal.continuousAt.comp hχ.continuousAt
    exact h1.mul (hf.continuousAt (hU.mem_nhds hp))
  · have hχp : χ p = 0 := hzero p hp
    have hbdd : ∀ x, ‖(χ x : ℂ) * f x‖ ≤ |χ x| * B := by
      intro x
      by_cases hx : x ∈ U
      · rw [norm_mul, Complex.norm_real]
        exact mul_le_mul_of_nonneg_left (hB x hx) (abs_nonneg _)
      · rw [hzero x hx]; simp
    have hlim : Tendsto (fun x => |χ x| * B) (𝓝 p) (𝓝 0) := by
      have h0 : Tendsto (fun x => |χ x|) (𝓝 p) (𝓝 0) := by
        have h := (hχ.continuousAt (x := p)).abs
        rw [show (0:ℝ) = |χ p| by rw [hχp, abs_zero]]
        exact h
      simpa using h0.mul_const B
    have key : Tendsto (fun x : X => ‖(χ x : ℂ) * f x‖) (𝓝 p) (𝓝 0) :=
      squeeze_zero (fun x => norm_nonneg _) hbdd hlim
    rw [ContinuousAt, show (χ p : ℂ) * f p = 0 by rw [hχp]; simp]
    rwa [tendsto_zero_iff_norm_tendsto_zero]

/-- **Real-part bounds for the Green–Tao region `ZetaReg β`.**  If `ZetaReg β z` then
`-(β / log 2) ≤ re z ≤ 1`; the lower bound is the *worst case* of the logarithmic boundary
`-β / log(|im z| + 2)` (attained at `im z = 0`). -/
theorem ZetaReg_re_bounds {β : ℝ} (hβ : 0 < β) {z : ℂ} (hz : ZetaReg β z) :
    -(β / Real.log 2) ≤ z.re ∧ z.re ≤ 1 := by
  refine ⟨?_, hz.2⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log (|z.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg z.im])
  have h2 : β / Real.log (|z.im| + 2) ≤ β / Real.log 2 :=
    div_le_div_of_nonneg_left hβ.le hlog2 hle
  linarith [hz.1]

/-- A `ZetaReg`-vector lies in the box `[a, b]^m` as soon as `a ≤ -(β / log 2)` and `1 ≤ b`. -/
theorem ZetaRegVec_between {β a b : ℝ} {m : ℕ} (ha : a ≤ -(β / Real.log 2)) (hb : 1 ≤ b)
    (hβ : 0 < β) {z : Fin m → ℂ} (hz : ZetaRegVec β z) :
    ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b :=
  fun i => ⟨le_trans ha (ZetaReg_re_bounds hβ (hz i)).1,
    le_trans (ZetaReg_re_bounds hβ (hz i)).2 hb⟩

/-- Strict version of `ZetaRegVec_between`. -/
theorem ZetaRegVec_between_strict {β a b : ℝ} {m : ℕ} (ha : a < -(β / Real.log 2)) (hb : 1 < b)
    (hβ : 0 < β) {z : Fin m → ℂ} (hz : ZetaRegVec β z) :
    ∀ i, a < (z i).re ∧ (z i).re < b :=
  fun i => ⟨lt_of_lt_of_le ha (ZetaReg_re_bounds hβ (hz i)).1,
    lt_of_le_of_lt (ZetaReg_re_bounds hβ (hz i)).2 hb⟩

/-- **The open strip `{∀ i, -σ < re z_i < 100}` in `ℂ^m` (and in `ℂ^m × ℂ^m`) is open.** -/
theorem isOpen_stripSet (m : ℕ) (σ : ℝ) :
    IsOpen {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
      (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)} := by
  have hleft : IsOpen {z : Fin m → ℂ | ∀ i, -σ < (z i).re ∧ (z i).re < 100} := by
    have hset : {z : Fin m → ℂ | ∀ i, -σ < (z i).re ∧ (z i).re < 100}
        = Set.pi Set.univ (fun _ : Fin m => {w : ℂ | -σ < w.re ∧ w.re < 100}) := by
      ext z; simp [Set.mem_pi]
    rw [hset]
    refine isOpen_set_pi Set.finite_univ (fun i _ => ?_)
    exact (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hset : {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
      (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)}
      = {z : Fin m → ℂ | ∀ i, -σ < (z i).re ∧ (z i).re < 100}
        ×ˢ {z : Fin m → ℂ | ∀ i, -σ < (z i).re ∧ (z i).re < 100} := by
    ext p; simp [Set.mem_prod]
  rw [hset]
  exact hleft.prod hleft

/-- Pointwise box membership for a vector with one coordinate updated. -/
theorem mem_boxSet_update {a b : ℝ} {m : ℕ} {z : Fin m → ℂ} (hz : ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b)
    {j : Fin m} {u : ℂ} (hu : a ≤ u.re ∧ u.re ≤ b) :
    ∀ i, a ≤ ((Function.update z j u) i).re ∧ ((Function.update z j u) i).re ≤ b := by
  intro i
  rcases eq_or_ne i j with h | h
  · subst h; rw [Function.update_self]; exact hu
  · rw [Function.update_of_ne h]; exact hz i

/-- **The closed box `{∀ i, a ≤ re z_i ≤ b}` in `ℂ^m × ℂ^m` is closed.** -/
theorem isClosed_boxSet (m : ℕ) (a b : ℝ) :
    IsClosed {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
      (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} := by
  have hleft : IsClosed {z : Fin m → ℂ | ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b} := by
    have hset : {z : Fin m → ℂ | ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b}
        = Set.pi Set.univ (fun _ : Fin m => {w : ℂ | a ≤ w.re ∧ w.re ≤ b}) := by
      ext z; simp [Set.mem_pi]
    rw [hset]
    refine isClosed_set_pi (fun i _ => ?_)
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_le Complex.continuous_re continuous_const)
  have hset : {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
      (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)}
      = {z : Fin m → ℂ | ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b}
        ×ˢ {z : Fin m → ℂ | ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b} := by
    ext p; simp [Set.mem_prod]
  rw [hset]
  exact hleft.prod hleft

/-- **`zetaMmf` only sees the values of `F` on the contour `Γ₁^m × Γ₁^m`.** -/
theorem zetaMmf_congr {R : ℝ} {m : ℕ} {F F' : (Fin m → ℂ) → (Fin m → ℂ) → ℂ}
    (h : ∀ (t t' : Fin m → ℝ), F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
      = F' (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))) :
    zetaMmf R m F = zetaMmf R m F' := by
  unfold zetaMmf
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
  simp only [h t t']


set_option maxHeartbeats 1000000 in
/-- The same statement as `Commons.NumberTheory.Zeta.zeta_bound_m_strip`, but the continuity hypothesis on `F` is required only on the OPEN STRIP `S_σ := {p : (Fin m → ℂ) × (Fin m → ℂ) | (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧ (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)}` instead of globally on `ℂ^m × ℂ^m`.  This is the version needed for the Green–Tao §10 application: the function actually fed in is `F = G₁G₂ = ∏_p E_p^{(1)} · ∏_p E_p^{(2)}`, an Euler product which converges (locally uniformly) exactly on the half-space `Re > -1/(6m)`, so it is continuous on the strip but NOT globally continuous.  PROOF SKETCH: copy the proof of `zeta_bound_m_strip` verbatim -- it only ever uses `hcont` inside the strip (for the Fubini interchange on `Γ₁ × Γ₁ ⊆ S_σ` and for the induction step, where the function integrated out is again continuous on the strip by dominated convergence).  All the "differentiable in each variable" hypotheses below are already restricted to the strip, exactly as in `zeta_bound_m_strip`. -/
theorem zeta_bound_m_strip_continuousOn (m : ℕ) (hm : 1 ≤ m) :
    ∃ σ δ C : ℝ, 0 < σ ∧ 0 < δ ∧ 0 < C ∧
      ∀ R : ℝ, 3 ≤ R → ∀ F : (Fin m → ℂ) → (Fin m → ℂ) → ℂ, ∀ B : ℝ, 0 ≤ B →
      ContinuousOn (Function.uncurry F)
        {p : (Fin m → ℂ) × (Fin m → ℂ) |
          (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
          (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)} →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -σ < (z i).re ∧ (z i).re < 100) →
        (∀ i, -σ < (z' i).re ∧ (z' i).re < 100) →
        DifferentiableAt ℂ (fun u : ℂ => F (Function.update z j u) z') (z j)) →
      (∀ (j : Fin m) (z z' : Fin m → ℂ),
        (∀ i, -σ < (z i).re ∧ (z i).re < 100) →
        (∀ i, -σ < (z' i).re ∧ (z' i).re < 100) →
        DifferentiableAt ℂ (fun u : ℂ => F z (Function.update z' j u)) (z' j)) →
      (∀ z z' : Fin m → ℂ,
        (∀ i, -σ < (z i).re ∧ (z i).re < 100) →
        (∀ i, -σ < (z' i).re ∧ (z' i).re < 100) →
        ‖F z z'‖ ≤ B) →
      ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ (2 * m) *
          (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
            F (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
              (fun j => Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
            * (∏ j, (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                    + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j))
                  / (riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t j))
                      * riemannZeta (1 + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))))
            * (R : ℂ) ^ (∑ j, (Commons.NumberTheory.Zeta.zetaM1Eta R (t j)
                + Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)))
            * (∏ j, ((Commons.NumberTheory.Zeta.zetaM1Eta R (t j)) ^ 2
                  * (Commons.NumberTheory.Zeta.zetaM1Eta R (t' j)) ^ 2)⁻¹)
            * Complex.I ^ m * Complex.I ^ m)
        - F 0 0 * (Real.log R) ^ m‖
        ≤ C ^ m * B * (1 + (Real.log R) ^ (m - 1))
          + C ^ m * B * Real.exp (-(δ * Real.sqrt (Real.log R))) := by
  obtain ⟨β₀, D₀, hβ₀pos, hβ₀10⟩ := zetaAux_exists
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmR : (0:ℝ) < (m:ℝ) := Nat.cast_pos.mpr (by omega)
  set σ : ℝ := 1 / (6 * (m:ℝ)) with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; positivity
  have hσle : σ ≤ 1 / 6 := by
    rw [hσdef]
    refine one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 6) ?_
    have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  set β : ℝ := min β₀ (Real.log 2 / (12 * (m:ℝ))) with hβdef
  have hβpos : 0 < β := by
    rw [hβdef]; exact lt_min hβ₀pos (div_pos hlog2pos (by positivity))
  have hβle : β ≤ β₀ := by rw [hβdef]; exact min_le_left _ _
  have hβ10 : β ≤ 1 / 10 := le_trans hβle hβ₀10
  have hβσ : β / Real.log 2 < σ := by
    rw [hβdef, hσdef, div_lt_iff₀ hlog2pos]
    calc min β₀ (Real.log 2 / (12 * (m:ℝ))) ≤ Real.log 2 / (12 * (m:ℝ)) := min_le_right _ _
      _ < Real.log 2 / (6 * (m:ℝ)) :=
          div_lt_div_of_pos_left hlog2pos (by positivity) (by nlinarith [hmR])
      _ = (1 / (6 * (m:ℝ))) * Real.log 2 := by ring
  obtain ⟨hD⟩ : Nonempty (ZetaAux β) := zetaAux_le D₀ hβ₀pos hβ₀10 hβpos hβ10 hβle
  obtain ⟨C, hC1, hCbound⟩ := zetaMmf_bound hD hβpos hβ10
  refine ⟨σ, 1, C, hσpos, one_pos, lt_of_lt_of_le one_pos hC1, ?_⟩
  intro R hR F B hB hcontOn hd1 hd2 hbound
  have hRne : (R : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by linarith : (0:ℝ) < R))
  have hβlog2pos : 0 < β / Real.log 2 := div_pos hβpos hlog2pos
  have hUopen := isOpen_stripSet m σ
  set θ : ℝ := (σ - β / Real.log 2) / 2 with hθdef
  have hθpos : 0 < θ := by rw [hθdef]; linarith
  set a : ℝ := -(β / Real.log 2) - θ with hadef
  set b : ℝ := 1 + θ with hbdef
  have hale : a ≤ -(β / Real.log 2) := by rw [hadef]; linarith
  have halt : a < -(β / Real.log 2) := by rw [hadef]; linarith
  have hbge : 1 ≤ b := by rw [hbdef]; linarith
  have hbgt : 1 < b := by rw [hbdef]; linarith
  have hagt : -σ < a := by rw [hadef, hθdef]; linarith
  have hblt : b < 100 := by rw [hbdef, hθdef]; linarith
  have hAclosed := isClosed_boxSet m a b
  have hAU : {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
      (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} ⊆
      {p : (Fin m → ℂ) × (Fin m → ℂ) |
        (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
        (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)} := by
    intro p hp
    exact ⟨fun i => ⟨lt_of_lt_of_le hagt (hp.1 i).1, lt_of_le_of_lt (hp.1 i).2 hblt⟩,
      fun i => ⟨lt_of_lt_of_le hagt (hp.2 i).1, lt_of_le_of_lt (hp.2 i).2 hblt⟩⟩
  have hUclosed : IsClosed {p : (Fin m → ℂ) × (Fin m → ℂ) |
      (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
      (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)}ᶜ := isClosed_compl_iff.mpr hUopen
  obtain ⟨χ, hχ0, hχ1, _⟩ := exists_continuous_zero_one_of_isClosed
    hUclosed hAclosed (disjoint_compl_right.mono_left hAU).symm
  let F' : (Fin m → ℂ) → (Fin m → ℂ) → ℂ := fun z z' => ((χ (z, z') : ℝ) : ℂ) * F z z'
  have hF'eq : Function.uncurry F'
      = fun p : (Fin m → ℂ) × (Fin m → ℂ) => ((χ p : ℝ) : ℂ) * F p.1 p.2 := by
    funext p
    simp only [Function.uncurry, F', Prod.mk.eta]
  have hAdm : ZetaAdm β m F' B := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hF'eq]
      refine continuous_ofReal_mul_of_continuousOn (fun p => (χ p : ℝ)) (fun p => F p.1 p.2)
        {p : (Fin m → ℂ) × (Fin m → ℂ) |
          (∀ i, -σ < (p.1 i).re ∧ (p.1 i).re < 100) ∧
          (∀ i, -σ < (p.2 i).re ∧ (p.2 i).re < 100)} B χ.continuous hcontOn hUopen ?_ ?_
      · intro p hp; exact hχ0 hp
      · intro p hp; exact hbound p.1 p.2 hp.1 hp.2
    · intro j z z' hz hz'
      have hzs : ∀ i, -σ < (z i).re ∧ (z i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i)
      have hz's : ∀ i, -σ < (z' i).re ∧ (z' i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i)
      have hzA := ZetaRegVec_between hale hbge hβpos hz
      have hz'A := ZetaRegVec_between hale hbge hβpos hz'
      have hzS := ZetaRegVec_between_strict halt hbgt hβpos hz
      have heq : (fun u : ℂ => F (Function.update z j u) z') =ᶠ[𝓝 (z j)]
          (fun u : ℂ =>
            ((χ (Function.update z j u, z') : ℝ) : ℂ) * F (Function.update z j u) z') := by
        have hmem : Set.Ioo a b ∈ 𝓝 ((z j).re) := isOpen_Ioo.mem_nhds ⟨(hzS j).1, (hzS j).2⟩
        have hev : ∀ᶠ u : ℂ in 𝓝 (z j), u.re ∈ Set.Ioo a b :=
          (Complex.continuous_re.continuousAt (x := z j)).preimage_mem_nhds hmem
        filter_upwards [hev] with u hu
        have hinA : (Function.update z j u, z') ∈ {p : (Fin m → ℂ) × (Fin m → ℂ) |
            (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
            (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} :=
          ⟨mem_boxSet_update hzA ⟨hu.1.le, hu.2.le⟩, hz'A⟩
        rw [hχ1 hinA]; simp
      exact (hd1 j z z' hzs hz's).congr_of_eventuallyEq heq.symm
    · intro j z z' hz hz'
      have hzs : ∀ i, -σ < (z i).re ∧ (z i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i)
      have hz's : ∀ i, -σ < (z' i).re ∧ (z' i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i)
      have hzA := ZetaRegVec_between hale hbge hβpos hz
      have hz'A := ZetaRegVec_between hale hbge hβpos hz'
      have hz'S := ZetaRegVec_between_strict halt hbgt hβpos hz'
      have heq : (fun u : ℂ => F z (Function.update z' j u)) =ᶠ[𝓝 (z' j)]
          (fun u : ℂ =>
            ((χ (z, Function.update z' j u) : ℝ) : ℂ) * F z (Function.update z' j u)) := by
        have hmem : Set.Ioo a b ∈ 𝓝 ((z' j).re) := isOpen_Ioo.mem_nhds ⟨(hz'S j).1, (hz'S j).2⟩
        have hev : ∀ᶠ u : ℂ in 𝓝 (z' j), u.re ∈ Set.Ioo a b :=
          (Complex.continuous_re.continuousAt (x := z' j)).preimage_mem_nhds hmem
        filter_upwards [hev] with u hu
        have hinA : (z, Function.update z' j u) ∈ {p : (Fin m → ℂ) × (Fin m → ℂ) |
            (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧
            (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)} :=
          ⟨hzA, mem_boxSet_update hz'A ⟨hu.1.le, hu.2.le⟩⟩
        rw [hχ1 hinA]; simp
      exact (hd2 j z z' hzs hz's).congr_of_eventuallyEq heq.symm
    · intro z z' hz hz'
      have hzs : ∀ i, -σ < (z i).re ∧ (z i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz i)
      have hz's : ∀ i, -σ < (z' i).re ∧ (z' i).re < 100 :=
        fun i => ZetaReg_subset_strip hβpos.le hβσ (hz' i)
      have hzA := ZetaRegVec_between hale hbge hβpos hz
      have hz'A := ZetaRegVec_between hale hbge hβpos hz'
      have hχz : χ (z, z') = 1 := hχ1 ⟨hzA, hz'A⟩
      show ‖((χ (z, z') : ℝ) : ℂ) * F z z'‖ ≤ B
      rw [hχz]; simp only [Complex.ofReal_one, one_mul]
      exact hbound z z' hzs hz's
  have hz : zetaMmf R m F = zetaMmf R m F' := by
    refine zetaMmf_congr (fun t t' => ?_)
    have h1 := ZetaRegVec_between hale hbge hβpos (ZetaRegVec_eta (R := R) hβpos hR t)
    have h2 := ZetaRegVec_between hale hbge hβpos (ZetaRegVec_eta (R := R) hβpos hR t')
    have hχ1' : χ ((fun j => zetaM1Eta R (t j)), (fun j => zetaM1Eta R (t' j))) = 1 :=
      hχ1 ⟨h1, h2⟩
    show F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
        = ((χ ((fun j => zetaM1Eta R (t j)), (fun j => zetaM1Eta R (t' j))) : ℝ) : ℂ)
          * F (fun j => zetaM1Eta R (t j)) (fun j => zetaM1Eta R (t' j))
    rw [hχ1']; simp
  have hz00 : F' 0 0 = F 0 0 := by
    have h0 : χ (((0 : Fin m → ℂ)), ((0 : Fin m → ℂ))) = 1 := by
      apply hχ1
      constructor
      · intro i
        simp only [Pi.zero_apply, Complex.zero_re]
        exact ⟨by linarith [hale, hβlog2pos], by linarith [hbge]⟩
      · intro i
        simp only [Pi.zero_apply, Complex.zero_re]
        exact ⟨by linarith [hale, hβlog2pos], by linarith [hbge]⟩
    show ((χ (((0 : Fin m → ℂ)), ((0 : Fin m → ℂ))) : ℝ) : ℂ) * F 0 0 = F 0 0
    rw [h0]; simp
  have hb := hCbound R hR m hm F' B hB hAdm
  rw [← zetaMmf_eq_explicit hRne m F, hz, ← hz00]
  exact le_trans hb (le_add_of_nonneg_right (mul_nonneg
    (mul_nonneg (pow_nonneg (le_of_lt (lt_of_lt_of_le one_pos hC1)) m) hB)
    (Real.exp_pos _).le))

end Commons.NumberTheory.Zeta

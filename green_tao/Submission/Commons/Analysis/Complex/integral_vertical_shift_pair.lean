import Mathlib.MeasureTheory.Integral.Pi
import Submission.Commons.Analysis.Complex.vertical_contour_shift

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace Commons.Analysis.Complex

noncomputable section

/-! ## The vertical parametrisation of `ℂ^m`, strips, and slices -/

/-- The point of `ℂ^m` whose real parts are given by `u` and whose imaginary parts are
given by `t`. -/
def vertPt {m : ℕ} (u : Fin m → ℝ) (t : Fin m → ℝ) : Fin m → ℂ :=
  fun i => (u i : ℂ) + (t i : ℂ) * Complex.I

@[simp] lemma vertPt_apply {m : ℕ} (u : Fin m → ℝ) (t : Fin m → ℝ) (i : Fin m) :
    vertPt u t i = (u i : ℂ) + (t i : ℂ) * Complex.I := rfl

@[simp] lemma vertPt_re {m : ℕ} (u : Fin m → ℝ) (t : Fin m → ℝ) (i : Fin m) :
    (vertPt u t i).re = u i := by simp [vertPt]

@[simp] lemma vertPt_im {m : ℕ} (u : Fin m → ℝ) (t : Fin m → ℝ) (i : Fin m) :
    (vertPt u t i).im = t i := by simp [vertPt]

/-- The tail of a vector indexed by `Fin (n+1)`. -/
def tailU {n : ℕ} (u : Fin (n+1) → ℝ) : Fin n → ℝ := fun i => u i.succ

@[simp] lemma tailU_apply {n : ℕ} (u : Fin (n+1) → ℝ) (i : Fin n) : tailU u i = u i.succ := rfl

/-- Updating a `Fin.cons` at a successor index. -/
lemma update_cons_succ {n : ℕ} (a : ℂ) (z : Fin n → ℂ) (j : Fin n) (u : ℂ) :
    Function.update (Fin.cons (α := fun _ => ℂ) a z) j.succ u
      = Fin.cons (α := fun _ => ℂ) a (Function.update z j u) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [Function.update_apply, Ne.symm (Fin.succ_ne_zero j)]
  | succ k => simp [Function.update_apply, Fin.succ_inj]

/-- The vertical strip `{z : Fin m → ℂ | ∀ i, a ≤ (z i).re ≤ b}`. -/
def strip {m : ℕ} (a b : ℝ) : Set (Fin m → ℂ) := {z | ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b}

/-- The product of two vertical strips (the domain of the two-variable integrand). -/
def stripPair {m : ℕ} (a b : ℝ) : Set ((Fin m → ℂ) × (Fin m → ℂ)) :=
  {p | (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧ (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)}

@[simp] lemma mem_strip {m : ℕ} {a b : ℝ} {z : Fin m → ℂ} :
    z ∈ strip a b ↔ ∀ i, a ≤ (z i).re ∧ (z i).re ≤ b := Iff.rfl

@[simp] lemma mem_stripPair {m : ℕ} {a b : ℝ} {p : (Fin m → ℂ) × (Fin m → ℂ)} :
    p ∈ stripPair a b ↔
      (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧ (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b) :=
  Iff.rfl

/-! ## Generic measure-theoretic helpers -/

/-- Fubini decomposition of an integral over `Fin (n+1) → ℝ`. -/
theorem integral_fin_succ {n : ℕ} (F : (Fin (n+1) → ℝ) → ℂ) (hF : Integrable F) :
    (∫ t : Fin (n+1) → ℝ, F t) = ∫ s : ℝ, ∫ t' : Fin n → ℝ, F (Fin.cons s t') := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n+1) → ℝ) := (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  have hem : MeasurePreserving (e : ℝ × (Fin n → ℝ) → (Fin (n+1) → ℝ)) :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  have hint : Integrable (fun p : ℝ × (Fin n → ℝ) => F (e p))
      ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    rw [← Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact (hem.integrable_comp_emb e.measurableEmbedding).2 hF
  have step : (∫ p : ℝ × (Fin n → ℝ), F (e p))
      = ∫ s : ℝ, ∫ t' : Fin n → ℝ, F (e (s, t')) := by
    rw [show (volume : Measure (ℝ × (Fin n → ℝ)))
        = (volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)) from
        Measure.volume_eq_prod ℝ (Fin n → ℝ)]
    exact integral_prod _ hint
  rw [← hem.integral_comp' F, step]
  congr 1 with s
  congr 1 with t'
  simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  congr 1
  funext j
  simp

/-- Integrability of a function `ℝ → ℂ` from a bound by a multiple of an integrable function. -/
lemma integrable_of_norm_le_mul {f : ℝ → ℂ} {K : ℝ} (_hK : 0 ≤ K) {g : ℝ → ℝ}
    (hgint : Integrable g) (hmeas : AEStronglyMeasurable f volume)
    (hb : ∀ t, ‖f t‖ ≤ K * g t) : Integrable f :=
  Integrable.mono' (hgint.const_mul K) hmeas (by filter_upwards with t; exact hb t)

/-- Integrability on `Fin m → ℝ` from a bound by a product of integrable functions. -/
lemma integrable_of_norm_le_prod {m : ℕ} {f : (Fin m → ℝ) → ℂ} {K : ℝ} (_hK : 0 ≤ K)
    {g : ℝ → ℝ} (hgint : Integrable g) (hmeas : AEStronglyMeasurable f volume)
    (hb : ∀ t, ‖f t‖ ≤ K * ∏ i, g (t i)) : Integrable f := by
  refine Integrable.mono' (g := fun t : Fin m → ℝ => K * ∏ i, g (t i)) ?_ hmeas ?_
  · exact (Integrable.fintype_prod (fun _ : Fin m => hgint)).const_mul K
  · filter_upwards with t; exact hb t

/-- Integrability on `ℝ × (Fin n → ℝ)` from a bound by a product of integrable functions. -/
lemma integrable_of_norm_le_prod_mul {n : ℕ} {f : ℝ × (Fin n → ℝ) → ℂ} {K : ℝ} (_hK : 0 ≤ K)
    {g : ℝ → ℝ} (hgint : Integrable g)
    (hmeas : AEStronglyMeasurable f ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))))
    (hb : ∀ p, ‖f p‖ ≤ K * (g p.1 * ∏ i, g (p.2 i))) :
    Integrable f ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
  refine Integrable.mono' (g := fun p : ℝ × (Fin n → ℝ) => K * (g p.1 * ∏ i, g (p.2 i))) ?_ hmeas ?_
  · exact (Integrable.mul_prod hgint (Integrable.fintype_prod (fun _ : Fin n => hgint))).const_mul K
  · filter_upwards with p; exact hb p

/-- Integrability on `(Fin m → ℝ) × (Fin m → ℝ)` from a bound by a product of integrable
functions. -/
lemma integrable_of_norm_le_prod_fin {m : ℕ} {f : (Fin m → ℝ) × (Fin m → ℝ) → ℂ} {K : ℝ}
    (_hK : 0 ≤ K) {g : ℝ → ℝ} (hgint : Integrable g)
    (hmeas : AEStronglyMeasurable f
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin m → ℝ))))
    (hb : ∀ p, ‖f p‖ ≤ K * ((∏ i, g (p.1 i)) * ∏ i, g (p.2 i))) :
    Integrable f ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin m → ℝ))) := by
  refine Integrable.mono' (g := fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
    K * ((∏ i, g (p.1 i)) * ∏ i, g (p.2 i))) ?_ hmeas ?_
  · have hbase : Integrable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        (∏ i, g (p.1 i)) * (∏ i, g (p.2 i)))
        ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin m → ℝ))) :=
      (Integrable.fintype_prod (fun _ : Fin m => hgint)).mul_prod
        (Integrable.fintype_prod (fun _ : Fin m => hgint))
    exact hbase.const_mul K
  · filter_upwards with p; exact hb p

/-- Horizontal decay of interval integrals, via a pointwise bound. -/
theorem tendsto_intervalIntegral_of_bound_aux {f : ℝ → ℝ → ℂ} {g : ℝ → ℝ} {p q K : ℝ}
    (_hK : 0 ≤ K) (hg : Tendsto g atTop (nhds 0))
    (hb : ∀ R x, x ∈ Set.uIoc p q → ‖f R x‖ ≤ K * g R) :
    Tendsto (fun R : ℝ => ∫ x in p..q, f R x) atTop (nhds 0) := by
  have hlim : Tendsto (fun R : ℝ => K * g R * |q - p|) atTop (nhds 0) := by
    have h := hg.const_mul (K * |q - p|)
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun R => norm_nonneg _) (fun R => ?_) hlim
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => hb R x hx)

/-- Continuity of `t ↦ Φ (fun i => u i + t i * I)` on `Fin m → ℝ`. -/
lemma continuous_comp_vertical {m : ℕ} {a b : ℝ} {Φ : (Fin m → ℂ) → ℂ}
    (hcont : ContinuousOn Φ (strip a b)) {u : Fin m → ℝ} (hu : ∀ i, a ≤ u i ∧ u i ≤ b) :
    Continuous (fun t : Fin m → ℝ => Φ (vertPt u t)) := by
  have h1 : Continuous (fun t : Fin m → ℝ => (vertPt u t : Fin m → ℂ)) := by
    refine continuous_pi (fun i => ?_)
    simp only [vertPt_apply]
    fun_prop
  refine hcont.comp_continuous h1 ?_
  intro t
  rw [mem_strip]
  intro i
  simpa using hu i

/-- Continuity of a slice through index `0`. -/
lemma continuous_comp_cons {n : ℕ} {a b : ℝ} {Φ : (Fin (n+1) → ℂ) → ℂ}
    (hcont : ContinuousOn Φ (strip a b)) {rest : Fin n → ℂ} (hrest : rest ∈ strip a b)
    {f : ℝ → ℂ} (hf : Continuous f) (hfstrip : ∀ s, a ≤ (f s).re ∧ (f s).re ≤ b) :
    Continuous (fun s : ℝ => Φ (Fin.cons (α := fun _ => ℂ) (f s) rest)) := by
  have h1 : Continuous (fun s : ℝ => (Fin.cons (α := fun _ => ℂ) (f s) rest : Fin (n+1) → ℂ)) := by
    fun_prop
  refine hcont.comp_continuous h1 ?_
  intro s
  rw [mem_strip]
  intro i
  induction i using Fin.cases with
  | zero => simpa using hfstrip s
  | succ j => simpa using hrest j

/-- Horizontal decay for a slice of a function of `Fin (n+1)` variables, along a family of
horizontal lines whose heights are given by `tilt`. -/
lemma tendsto_horizontal_slice {n : ℕ} {a b : ℝ} {Φ : (Fin (n+1) → ℂ) → ℂ} {C : ℝ}
    (hC : 0 ≤ C) {g : ℝ → ℝ} (_hg0 : ∀ t, 0 ≤ g t) {tilt : ℝ → ℝ}
    (hgdec : Tendsto (fun R => g (tilt R)) atTop (nhds 0))
    (hbnd : ∀ z : Fin (n+1) → ℂ, z ∈ strip a b → ‖Φ z‖ ≤ C * ∏ i, g ((z i).im))
    {rest : Fin n → ℂ} (hrest : rest ∈ strip a b)
    {p q : ℝ} (hpq : p ≤ q) (hp : a ≤ p) (hqb : q ≤ b) :
    Tendsto (fun R : ℝ =>
      ∫ x in p..q, Φ (Fin.cons (α := fun _ => ℂ) ((x : ℂ) + (tilt R : ℂ) * Complex.I) rest))
      atTop (nhds 0) := by
  refine tendsto_intervalIntegral_of_bound_aux (K := C * ∏ i, g ((rest i).im)) ?_ hgdec ?_
  · exact mul_nonneg hC (Finset.prod_nonneg (fun i _ => _hg0 _))
  · intro R x hx
    rw [Set.uIoc_of_le hpq, Set.mem_Ioc] at hx
    have hxa : a ≤ x ∧ x ≤ b := ⟨le_trans hp hx.1.le, le_trans hx.2 hqb⟩
    have hstrip : Fin.cons (α := fun _ => ℂ) ((x : ℂ) + (tilt R : ℂ) * Complex.I) rest ∈ strip a b := by
      rw [mem_strip]
      intro i
      induction i using Fin.cases with
      | zero => simpa using hxa
      | succ j => simpa using hrest j
    calc ‖Φ (Fin.cons (α := fun _ => ℂ) ((x : ℂ) + (tilt R : ℂ) * Complex.I) rest)‖
        ≤ C * ∏ i, g ((Fin.cons (α := fun _ => ℂ) ((x : ℂ) + (tilt R : ℂ) * Complex.I) rest i).im) :=
          hbnd _ hstrip
      _ = (C * ∏ i, g ((rest i).im)) * g (tilt R) := by
          rw [Fin.prod_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Complex.add_im, Complex.mul_im,
            Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one,
            zero_add, add_zero]
          ring_nf

/-! ## Splitting an integral over `Fin (n+1) → ℝ` at coordinate `0` -/

private lemma integral_split_cons {n : ℕ} {a b : ℝ} {Φ : (Fin (n+1) → ℂ) → ℂ} {C : ℝ}
    (hC : 0 ≤ C) {g : ℝ → ℝ} (hgint : Integrable g)
    (hbnd : ∀ z : Fin (n+1) → ℂ, z ∈ strip a b → ‖Φ z‖ ≤ C * ∏ i, g ((z i).im))
    (hcont : ContinuousOn Φ (strip a b))
    {w : Fin (n+1) → ℝ} (hw : ∀ i, a ≤ w i ∧ w i ≤ b) :
    (∫ t : Fin (n+1) → ℝ, Φ (vertPt w t))
      = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU w) t')) := by
  have hInt : Integrable (fun t : Fin (n+1) → ℝ => Φ (vertPt w t)) := by
    refine integrable_of_norm_le_prod hC hgint
      (continuous_comp_vertical hcont hw).aestronglyMeasurable ?_
    intro t
    have h := hbnd (vertPt w t) (by rw [mem_strip]; intro i; simpa using hw i)
    simpa using h
  rw [integral_fin_succ _ hInt]
  congr 1 with s
  congr 1 with t'
  congr 1
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ j => simp

/-! ## Moving the base of a single coordinate -/

private theorem shift_coord0_aux {n : ℕ} {a b : ℝ}
    (Φ : (Fin (n+1) → ℂ) → ℂ) {C : ℝ} (hC : 0 ≤ C) {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgint : Integrable g)
    (hgdecTop : Tendsto g atTop (nhds 0)) (hgdecBot : Tendsto g atBot (nhds 0))
    (hbnd : ∀ z : Fin (n+1) → ℂ, z ∈ strip a b → ‖Φ z‖ ≤ C * ∏ i, g ((z i).im))
    (hcont : ContinuousOn Φ (strip a b))
    (hd : ∀ (j : Fin (n+1)) (z : Fin (n+1) → ℂ), z ∈ strip a b →
      DifferentiableAt ℂ (fun w : ℂ => Φ (Function.update z j w)) (z j))
    {u v : Fin (n+1) → ℝ} (hu : ∀ i, a ≤ u i ∧ u i ≤ b) (hv : ∀ i, a ≤ v i ∧ v i ≤ b)
    (huv : ∀ i, i ≠ 0 → u i = v i) :
    (∫ t : Fin (n+1) → ℝ, Φ (vertPt u t)) = ∫ t : Fin (n+1) → ℝ, Φ (vertPt v t) := by
  have huv' : tailU u = tailU v := by
    funext i; exact huv i.succ (Fin.succ_ne_zero i)
  have hUncurry : ∀ w : Fin (n+1) → ℝ, (∀ i, a ≤ w i ∧ w i ≤ b) →
      Integrable (Function.uncurry (fun s : ℝ => fun t' : Fin n → ℝ =>
          Φ (Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU w) t'))))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
    intro w hw
    refine integrable_of_norm_le_prod_mul hC hgint ?_ ?_
    · have hcont2 : Continuous (fun p : ℝ × (Fin n → ℝ) =>
          Φ (Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (p.1 : ℂ) * Complex.I) (vertPt (tailU w) p.2))) := by
        refine hcont.comp_continuous ?_ ?_
        · refine continuous_pi (fun i => ?_)
          induction i using Fin.cases with
          | zero => simp only [Fin.cons_zero]; fun_prop
          | succ j => simp only [Fin.cons_succ, vertPt_apply]; fun_prop
        · intro p
          rw [mem_strip]
          intro i
          induction i using Fin.cases with
          | zero => simpa using hw 0
          | succ j => simpa using hw j.succ
      exact hcont2.aestronglyMeasurable
    · intro p
      have hstrip : Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (p.1 : ℂ) * Complex.I)
          (vertPt (tailU w) p.2) ∈ strip a b := by
        rw [mem_strip]
        intro i
        induction i using Fin.cases with
        | zero => simpa using hw 0
        | succ j => simpa using hw j.succ
      calc ‖Φ (Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (p.1 : ℂ) * Complex.I) (vertPt (tailU w) p.2))‖
          ≤ C * ∏ i, g ((Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (p.1 : ℂ) * Complex.I) (vertPt (tailU w) p.2) i).im) :=
            hbnd _ hstrip
        _ = C * (g p.1 * ∏ i, g (p.2 i)) := by
            rw [Fin.prod_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ, vertPt_im, Complex.add_im, Complex.mul_im,
              Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one,
              zero_add, add_zero]
  have hswap : ∀ w : Fin (n+1) → ℝ, (∀ i, a ≤ w i ∧ w i ≤ b) →
      (∫ s : ℝ, ∫ t' : Fin n → ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU w) t')))
        = ∫ t' : Fin n → ℝ, ∫ s : ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((w 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU w) t')) :=
    fun w hw => integral_integral_swap (hUncurry w hw)
  have hslice : ∀ (p q : ℝ) (_hpq : p ≤ q) (hp : a ≤ p ∧ p ≤ b) (hq : a ≤ q ∧ q ≤ b)
      (t' : Fin n → ℝ),
      (∫ s : ℝ, Φ (Fin.cons (α := fun _ => ℂ) ((p : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')))
        = ∫ s : ℝ, Φ (Fin.cons (α := fun _ => ℂ) ((q : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) := by
    intro p q hpq hp hq t'
    have hrest : vertPt (tailU u) t' ∈ strip a b := by
      rw [mem_strip]; intro i; simpa using hu i.succ
    refine (vertical_contour_shift
      (F := fun w : ℂ => Φ (Fin.cons (α := fun _ => ℂ) w (vertPt (tailU u) t'))) p q hpq
      ?_ ?_ ?_ ?_ ?_).symm
    · intro R z hz
      rw [Complex.mem_reProdIm] at hz
      have hzre : a ≤ z.re ∧ z.re ≤ b := by
        rcases Set.mem_uIcc.mp hz.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans hp.1 h1, le_trans h2 hq.2⟩
        · exact ⟨le_trans hq.1 h1, le_trans h2 hp.2⟩
      have hstrip : Fin.cons (α := fun _ => ℂ) z (vertPt (tailU u) t') ∈ strip a b := by
        rw [mem_strip]
        intro i
        induction i using Fin.cases with
        | zero => simpa using hzre
        | succ j => simpa using hu j.succ
      have h := hd 0 (Fin.cons (α := fun _ => ℂ) z (vertPt (tailU u) t')) hstrip
      have h' : DifferentiableAt ℂ
          (fun x : ℂ => Φ (Fin.cons (α := fun _ => ℂ) x (vertPt (tailU u) t'))) z := by
        simpa [Fin.update_cons_zero, Fin.cons_zero] using h
      exact h'.differentiableWithinAt
    · refine integrable_of_norm_le_mul (K := C * ∏ i, g ((vertPt (tailU u) t' i).im)) ?_ hgint ?_ ?_
      · exact mul_nonneg hC (Finset.prod_nonneg (fun i _ => hg0 _))
      · exact (continuous_comp_cons hcont hrest (by fun_prop) (fun s => by simpa using hp)).aestronglyMeasurable
      · intro s
        have hstrip : Fin.cons (α := fun _ => ℂ) ((p : ℂ) + (s : ℂ) * Complex.I)
            (vertPt (tailU u) t') ∈ strip a b := by
          rw [mem_strip]
          intro i
          induction i using Fin.cases with
          | zero => simpa using hp
          | succ j => simpa using hu j.succ
        calc ‖Φ (Fin.cons (α := fun _ => ℂ) ((p : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t'))‖
            ≤ C * ∏ i, g ((Fin.cons (α := fun _ => ℂ) ((p : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t') i).im) :=
              hbnd _ hstrip
          _ = (C * ∏ i, g ((vertPt (tailU u) t' i).im)) * g s := by
              rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ, vertPt_im, Complex.add_im, Complex.mul_im,
                Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one,
                zero_add, add_zero]
              ring
    · refine integrable_of_norm_le_mul (K := C * ∏ i, g ((vertPt (tailU u) t' i).im)) ?_ hgint ?_ ?_
      · exact mul_nonneg hC (Finset.prod_nonneg (fun i _ => hg0 _))
      · exact (continuous_comp_cons hcont hrest (by fun_prop) (fun s => by simpa using hq)).aestronglyMeasurable
      · intro s
        have hstrip : Fin.cons (α := fun _ => ℂ) ((q : ℂ) + (s : ℂ) * Complex.I)
            (vertPt (tailU u) t') ∈ strip a b := by
          rw [mem_strip]
          intro i
          induction i using Fin.cases with
          | zero => simpa using hq
          | succ j => simpa using hu j.succ
        calc ‖Φ (Fin.cons (α := fun _ => ℂ) ((q : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t'))‖
            ≤ C * ∏ i, g ((Fin.cons (α := fun _ => ℂ) ((q : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t') i).im) :=
              hbnd _ hstrip
          _ = (C * ∏ i, g ((vertPt (tailU u) t' i).im)) * g s := by
              rw [Fin.prod_univ_succ]
              simp only [Fin.cons_zero, Fin.cons_succ, vertPt_im, Complex.add_im, Complex.mul_im,
                Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero, mul_one,
                zero_add, add_zero]
              ring
    · exact tendsto_horizontal_slice hC hg0 (tilt := fun R => R) (by simpa using hgdecTop)
        hbnd hrest hpq hp.1 hq.2
    · have hb := tendsto_horizontal_slice hC hg0 (tilt := fun R => -R)
        (by simpa [Function.comp_def] using hgdecBot.comp tendsto_neg_atTop_atBot)
        hbnd hrest hpq hp.1 hq.2
      simpa only [sub_eq_add_neg, Complex.ofReal_neg, neg_mul] using hb
  have hshift : ∀ t' : Fin n → ℝ,
      (∫ s : ℝ, Φ (Fin.cons (α := fun _ => ℂ) ((u 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')))
        = ∫ s : ℝ, Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) := by
    intro t'
    rcases le_total (u 0) (v 0) with hle | hle
    · exact hslice (u 0) (v 0) hle (hu 0) (hv 0) t'
    · exact (hslice (v 0) (u 0) hle (hv 0) (hu 0) t').symm
  calc (∫ t : Fin (n+1) → ℝ, Φ (vertPt u t))
      = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((u 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) :=
        integral_split_cons hC hgint hbnd hcont hu
    _ = ∫ t' : Fin n → ℝ, ∫ s : ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((u 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) :=
        hswap u hu
    _ = ∫ t' : Fin n → ℝ, ∫ s : ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) :=
        integral_congr_ae (Eventually.of_forall hshift)
    _ = ∫ t' : Fin n → ℝ, ∫ s : ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU v) t')) := by
        rw [huv']
    _ = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
          Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU v) t')) :=
        (hswap v hv).symm
    _ = ∫ t : Fin (n+1) → ℝ, Φ (vertPt v t) :=
        (integral_split_cons hC hgint hbnd hcont hv).symm

/-! ## The multi-dimensional vertical shift -/

theorem shift_all_fin : ∀ (m : ℕ) {a b : ℝ} (Φ : (Fin m → ℂ) → ℂ) {C : ℝ} (hC : 0 ≤ C)
    {g : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t) (hgint : Integrable g)
    (hgdecTop : Tendsto g atTop (nhds 0)) (hgdecBot : Tendsto g atBot (nhds 0))
    (hbnd : ∀ z : Fin m → ℂ, z ∈ strip a b → ‖Φ z‖ ≤ C * ∏ i, g ((z i).im))
    (hcont : ContinuousOn Φ (strip a b))
    (hd : ∀ (j : Fin m) (z : Fin m → ℂ), z ∈ strip a b →
      DifferentiableAt ℂ (fun w : ℂ => Φ (Function.update z j w)) (z j))
    {u v : Fin m → ℝ} (hu : ∀ i, a ≤ u i ∧ u i ≤ b) (hv : ∀ i, a ≤ v i ∧ v i ≤ b),
    (∫ t : Fin m → ℝ, Φ (vertPt u t)) = ∫ t : Fin m → ℝ, Φ (vertPt v t) := by
  intro m
  induction m with
  | zero =>
      intro a b Φ C hC g hg0 hgint hgdecTop hgdecBot hbnd hcont hd u v hu hv
      refine integral_congr_ae (Eventually.of_forall (fun t => ?_))
      show Φ (vertPt u t) = Φ (vertPt v t)
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      intro a b Φ C hC g hg0 hgint hgdecTop hgdecBot hbnd hcont hd u v hu hv
      have hhead : (∫ t : Fin (n+1) → ℝ, Φ (vertPt u t))
          = ∫ t : Fin (n+1) → ℝ, Φ (vertPt (Fin.cons (α := fun _ => ℝ) (v 0) (tailU u)) t) := by
        refine shift_coord0_aux (a := a) (b := b)
          (v := Fin.cons (α := fun _ => ℝ) (v 0) (tailU u)) Φ hC hg0 hgint hgdecTop hgdecBot
          hbnd hcont hd hu ?_ ?_
        · intro i
          cases i using Fin.cases with
          | zero => simpa using hv 0
          | succ j => simpa using hu j.succ
        · intro i hi
          cases i using Fin.cases with
          | zero => exact absurd rfl hi
          | succ j => rfl
      have hsplit1 : (∫ t : Fin (n+1) → ℝ,
            Φ (vertPt (Fin.cons (α := fun _ => ℝ) (v 0) (tailU u)) t))
          = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
              Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) :=
        integral_split_cons hC hgint hbnd hcont (by
          intro i
          cases i using Fin.cases with
          | zero => simpa using hv 0
          | succ j => simpa using hu j.succ)
      have hIH : (∫ s : ℝ, ∫ t' : Fin n → ℝ,
              Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')))
          = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
              Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU v) t')) := by
        refine integral_congr_ae (Eventually.of_forall (fun s => ?_))
        refine ih (Φ := fun z : Fin n → ℂ =>
            Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z))
          (C := C * g s) (hC := mul_nonneg hC (hg0 s)) (hg0 := hg0) (hgint := hgint)
          (hgdecTop := hgdecTop) (hgdecBot := hgdecBot) ?_ ?_ ?_
          (hu := fun i => hu i.succ) (hv := fun i => hv i.succ)
        · intro z hz
          rw [mem_strip] at hz
          have hstrip : Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z ∈ strip a b := by
            rw [mem_strip]
            intro i
            induction i using Fin.cases with
            | zero => simpa using hv 0
            | succ j => simpa using hz j
          calc ‖Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z)‖
              ≤ C * ∏ i, g ((Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z i).im) :=
                hbnd _ hstrip
            _ = (C * g s) * ∏ i, g ((z i).im) := by
                rw [Fin.prod_univ_succ]
                simp only [Fin.cons_zero, Fin.cons_succ, vertPt_im, Complex.add_im, Complex.mul_im,
                  Complex.ofReal_im, Complex.I_im, Complex.ofReal_re, Complex.I_re, mul_zero,
                  mul_one, zero_add, add_zero]
                ring
        · refine hcont.comp ?_ ?_
          · -- continuity of `z ↦ Fin.cons ((v 0) + s I) z`
            have hc1 : Continuous (fun z : Fin n → ℂ =>
                (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z :
                  Fin (n+1) → ℂ)) := by
              refine continuous_pi (fun i => ?_)
              induction i using Fin.cases with
              | zero => simp only [Fin.cons_zero]; fun_prop
              | succ j => simp only [Fin.cons_succ]; fun_prop
            exact hc1.continuousOn
          · intro z hz
            rw [mem_strip] at hz ⊢
            intro i
            induction i using Fin.cases with
            | zero => simpa using hv 0
            | succ j => simpa using hz j
        · intro j z hz
          rw [mem_strip] at hz
          have hstrip : Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z ∈ strip a b := by
            rw [mem_strip]
            intro i
            induction i using Fin.cases with
            | zero => simpa using hv 0
            | succ j => simpa using hz j
          have h := hd j.succ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) z) hstrip
          have h' : DifferentiableAt ℂ
              (fun w : ℂ => Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I)
                (Function.update z j w))) (z j) := by
            simpa only [update_cons_succ, Fin.cons_succ] using h
          exact h'
      have hsplit2 : (∫ t : Fin (n+1) → ℝ, Φ (vertPt v t))
          = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
              Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU v) t')) :=
        integral_split_cons hC hgint hbnd hcont hv
      calc (∫ t : Fin (n+1) → ℝ, Φ (vertPt u t))
          = ∫ t : Fin (n+1) → ℝ, Φ (vertPt (Fin.cons (α := fun _ => ℝ) (v 0) (tailU u)) t) := hhead
        _ = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
              Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU u) t')) := hsplit1
        _ = ∫ s : ℝ, ∫ t' : Fin n → ℝ,
              Φ (Fin.cons (α := fun _ => ℂ) ((v 0 : ℂ) + (s : ℂ) * Complex.I) (vertPt (tailU v) t')) := hIH
        _ = ∫ t : Fin (n+1) → ℝ, Φ (vertPt v t) := hsplit2.symm

/-! ## The two-variable version -/

private lemma shift_second_arg {m : ℕ} {a b : ℝ} (hab : a ≤ b)
    {Ψ : (Fin m → ℂ) → (Fin m → ℂ) → ℂ} {Cg : ℝ} (hCg : 0 ≤ Cg) {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgint : Integrable g)
    (hgdecTop : Tendsto g atTop (nhds 0)) (hgdecBot : Tendsto g atBot (nhds 0))
    (hbnd : ∀ z z' : Fin m → ℂ, z ∈ strip a b → z' ∈ strip a b →
      ‖Ψ z z'‖ ≤ Cg * (∏ i, g ((z i).im)) * (∏ i, g ((z' i).im)))
    (hcont : ContinuousOn (Function.uncurry Ψ) (stripPair a b))
    (hd2 : ∀ (j : Fin m) (z z' : Fin m → ℂ), z ∈ strip a b → z' ∈ strip a b →
      DifferentiableAt ℂ (fun w : ℂ => Ψ z (Function.update z' j w)) (z' j))
    {z : Fin m → ℂ} (hz : z ∈ strip a b) :
    (∫ t' : Fin m → ℝ, Ψ z (vertPt (fun _ => a) t'))
      = ∫ t' : Fin m → ℝ, Ψ z (vertPt (fun _ => b) t') := by
  refine shift_all_fin m (Φ := fun z' => Ψ z z') (C := Cg * ∏ i, g ((z i).im))
    (hC := mul_nonneg hCg (Finset.prod_nonneg (fun i _ => hg0 _))) hg0 hgint hgdecTop hgdecBot
    ?_ ?_ ?_ (hu := fun i => ⟨le_rfl, hab⟩) (hv := fun i => ⟨hab, le_rfl⟩)
  · intro z' hz'
    have h := hbnd z z' hz hz'
    simpa using h
  · refine hcont.comp (f := fun z' : Fin m → ℂ => (z, z')) ?_ ?_
    · have hc : Continuous (fun z' : Fin m → ℂ => ((z, z') : (Fin m → ℂ) × (Fin m → ℂ))) :=
        continuous_const.prodMk continuous_id
      exact hc.continuousOn
    · intro z' hz'
      rw [mem_stripPair]
      exact ⟨by rwa [mem_strip] at hz, by rwa [mem_strip] at hz'⟩
  · intro j z' hz'
    exact hd2 j z z' hz (by rwa [mem_strip] at hz')

private lemma shift_first_arg {m : ℕ} {a b : ℝ} (hab : a ≤ b)
    {Ψ : (Fin m → ℂ) → (Fin m → ℂ) → ℂ} {Cg : ℝ} (hCg : 0 ≤ Cg) {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgint : Integrable g)
    (hgdecTop : Tendsto g atTop (nhds 0)) (hgdecBot : Tendsto g atBot (nhds 0))
    (hbnd : ∀ z z' : Fin m → ℂ, z ∈ strip a b → z' ∈ strip a b →
      ‖Ψ z z'‖ ≤ Cg * (∏ i, g ((z i).im)) * (∏ i, g ((z' i).im)))
    (hcont : ContinuousOn (Function.uncurry Ψ) (stripPair a b))
    (hd1 : ∀ (j : Fin m) (z z' : Fin m → ℂ), z ∈ strip a b → z' ∈ strip a b →
      DifferentiableAt ℂ (fun w : ℂ => Ψ (Function.update z j w) z') (z j))
    {z' : Fin m → ℂ} (hz' : z' ∈ strip a b) :
    (∫ t : Fin m → ℝ, Ψ (vertPt (fun _ => a) t) z')
      = ∫ t : Fin m → ℝ, Ψ (vertPt (fun _ => b) t) z' := by
  refine shift_all_fin m (Φ := fun z => Ψ z z') (C := Cg * ∏ i, g ((z' i).im))
    (hC := mul_nonneg hCg (Finset.prod_nonneg (fun i _ => hg0 _))) hg0 hgint hgdecTop hgdecBot
    ?_ ?_ ?_ (hu := fun i => ⟨le_rfl, hab⟩) (hv := fun i => ⟨hab, le_rfl⟩)
  · intro z hz
    have h := hbnd z z' hz hz'
    have h2 : Cg * (∏ i, g ((z i).im)) * (∏ i, g ((z' i).im))
        = (Cg * ∏ i, g ((z' i).im)) * (∏ i, g ((z i).im)) := by ring
    rw [h2] at h
    exact h
  · refine hcont.comp (f := fun z : Fin m → ℂ => (z, z')) ?_ ?_
    · have hc : Continuous (fun z : Fin m → ℂ => ((z, z') : (Fin m → ℂ) × (Fin m → ℂ))) :=
        continuous_id.prodMk continuous_const
      exact hc.continuousOn
    · intro z hz
      rw [mem_stripPair]
      exact ⟨by rwa [mem_strip] at hz, by rwa [mem_strip] at hz'⟩
  · intro j z hz
    exact hd1 j z z' (by rwa [mem_strip] at hz) hz'

/-! ## The two-variable vertical shift -/

private lemma vertPt_mem_strip {m : ℕ} {a b c : ℝ} (h1 : a ≤ c) (h2 : c ≤ b)
    (t : Fin m → ℝ) : vertPt (fun _ => c) t ∈ strip a b := by
  rw [mem_strip]
  intro i
  exact ⟨by simpa using h1, by simpa using h2⟩

private lemma pair_mem_stripPair {m : ℕ} {a b c d : ℝ} (h1 : a ≤ c) (h2 : c ≤ b)
    (h3 : a ≤ d) (h4 : d ≤ b) {p : (Fin m → ℝ) × (Fin m → ℝ)} :
    (vertPt (fun _ => c) p.1, vertPt (fun _ => d) p.2) ∈ stripPair a b := by
  rw [mem_stripPair]
  exact ⟨fun i => ⟨by simpa using h1, by simpa using h2⟩,
    fun i => ⟨by simpa using h3, by simpa using h4⟩⟩

private lemma integrable_double {m : ℕ} {a b : ℝ}
    {Ψ : (Fin m → ℂ) → (Fin m → ℂ) → ℂ} {Cg : ℝ} (hCg : 0 ≤ Cg) {g : ℝ → ℝ}
    (hgint : Integrable g)
    (hbnd' : ∀ z z' : Fin m → ℂ, z ∈ strip a b → z' ∈ strip a b →
      ‖Ψ z z'‖ ≤ Cg * (∏ i, g ((z i).im)) * (∏ i, g ((z' i).im)))
    (hcont' : ContinuousOn (Function.uncurry Ψ) (stripPair a b))
    {c d : ℝ} (h1 : a ≤ c) (h2 : c ≤ b) (h3 : a ≤ d) (h4 : d ≤ b) :
    Integrable (Function.uncurry (fun t t' : Fin m → ℝ =>
      Ψ (vertPt (fun _ => c) t) (vertPt (fun _ => d) t')))
      ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Fin m → ℝ))) := by
  refine integrable_of_norm_le_prod_fin (K := Cg) hCg hgint ?_ ?_
  · have hc : Continuous (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
        ((vertPt (fun _ => c) p.1, vertPt (fun _ => d) p.2) :
          (Fin m → ℂ) × (Fin m → ℂ))) := by
      refine Continuous.prodMk ?_ ?_
      · refine continuous_pi (fun i => ?_); simp only [vertPt_apply]; fun_prop
      · refine continuous_pi (fun i => ?_); simp only [vertPt_apply]; fun_prop
    exact (hcont'.comp_continuous hc (fun p => pair_mem_stripPair h1 h2 h3 h4)).aestronglyMeasurable
  · intro p
    have h := hbnd' _ _ (vertPt_mem_strip h1 h2 p.1) (vertPt_mem_strip h3 h4 p.2)
    rw [mul_assoc] at h
    simpa [Function.uncurry] using h

theorem integral_vertical_shift_pair {m : ℕ} {a b : ℝ} (hab : a ≤ b)
    (Ψ : (Fin m → ℂ) → (Fin m → ℂ) → ℂ) {Cg : ℝ} (hCg : 0 ≤ Cg) {g : ℝ → ℝ}
    (hg0 : ∀ t, 0 ≤ g t) (hgint : MeasureTheory.Integrable g)
    (hgdecTop : Filter.Tendsto g Filter.atTop (nhds 0))
    (hgdecBot : Filter.Tendsto g Filter.atBot (nhds 0))
    (hbnd : ∀ z z' : Fin m → ℂ,
      (∀ i, a ≤ (z i).re ∧ (z i).re ≤ b) → (∀ i, a ≤ (z' i).re ∧ (z' i).re ≤ b) →
      ‖Ψ z z'‖ ≤ Cg * (∏ i, g ((z i).im)) * (∏ i, g ((z' i).im)))
    (hcont : ContinuousOn (Function.uncurry Ψ)
      {p : (Fin m → ℂ) × (Fin m → ℂ) |
        (∀ i, a ≤ (p.1 i).re ∧ (p.1 i).re ≤ b) ∧ (∀ i, a ≤ (p.2 i).re ∧ (p.2 i).re ≤ b)})
    (hd1 : ∀ (j : Fin m) (z z' : Fin m → ℂ),
      (∀ i, a ≤ (z i).re ∧ (z i).re ≤ b) → (∀ i, a ≤ (z' i).re ∧ (z' i).re ≤ b) →
      DifferentiableAt ℂ (fun w : ℂ => Ψ (Function.update z j w) z') (z j))
    (hd2 : ∀ (j : Fin m) (z z' : Fin m → ℂ),
      (∀ i, a ≤ (z i).re ∧ (z i).re ≤ b) → (∀ i, a ≤ (z' i).re ∧ (z' i).re ≤ b) →
      DifferentiableAt ℂ (fun w : ℂ => Ψ z (Function.update z' j w)) (z' j)) :
    (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Ψ (fun i => (a : ℂ) + (t i : ℂ) * Complex.I)
          (fun i => (a : ℂ) + (t' i : ℂ) * Complex.I))
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Ψ (fun i => (b : ℂ) + (t i : ℂ) * Complex.I)
          (fun i => (b : ℂ) + (t' i : ℂ) * Complex.I) := by
  have hbnd' : ∀ z z' : Fin m → ℂ, z ∈ strip a b → z' ∈ strip a b →
      ‖Ψ z z'‖ ≤ Cg * (∏ i, g ((z i).im)) * (∏ i, g ((z' i).im)) :=
    fun z z' hz hz' => hbnd z z' hz hz'
  have hcont' : ContinuousOn (Function.uncurry Ψ) (stripPair a b) := hcont
  -- Step 1: shift the second argument, for each fixed value of the first.
  have hstep1 : ∀ t : Fin m → ℝ,
      (∫ t' : Fin m → ℝ, Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => a) t'))
        = ∫ t' : Fin m → ℝ, Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => b) t') := by
    intro t
    exact shift_second_arg hab hCg hg0 hgint hgdecTop hgdecBot hbnd' hcont' hd2
      (vertPt_mem_strip le_rfl hab t)
  have hL1 : (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => a) t'))
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => b) t') :=
    integral_congr_ae (Eventually.of_forall hstep1)
  have hInt_ab := integrable_double hCg hgint hbnd' hcont' le_rfl hab hab le_rfl
  have hswap1 : (∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => b) t'))
      = ∫ t' : Fin m → ℝ, ∫ t : Fin m → ℝ,
        Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => b) t') :=
    integral_integral_swap hInt_ab
  -- Step 2: shift the first argument, for each fixed value of the second.
  have hstep2 : ∀ t' : Fin m → ℝ,
      (∫ t : Fin m → ℝ, Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => b) t'))
        = ∫ t : Fin m → ℝ, Ψ (vertPt (fun _ => b) t) (vertPt (fun _ => b) t') := by
    intro t'
    exact shift_first_arg hab hCg hg0 hgint hgdecTop hgdecBot hbnd' hcont' hd1
      (vertPt_mem_strip hab le_rfl t')
  have hL2 : (∫ t' : Fin m → ℝ, ∫ t : Fin m → ℝ,
        Ψ (vertPt (fun _ => a) t) (vertPt (fun _ => b) t'))
      = ∫ t' : Fin m → ℝ, ∫ t : Fin m → ℝ,
        Ψ (vertPt (fun _ => b) t) (vertPt (fun _ => b) t') :=
    integral_congr_ae (Eventually.of_forall hstep2)
  have hInt_bb := integrable_double hCg hgint hbnd' hcont' hab le_rfl hab le_rfl
  have hswap2 : (∫ t' : Fin m → ℝ, ∫ t : Fin m → ℝ,
        Ψ (vertPt (fun _ => b) t) (vertPt (fun _ => b) t'))
      = ∫ t : Fin m → ℝ, ∫ t' : Fin m → ℝ,
        Ψ (vertPt (fun _ => b) t) (vertPt (fun _ => b) t') :=
    (integral_integral_swap hInt_bb).symm
  exact hL1.trans (hswap1.trans (hL2.trans hswap2))

end

end Commons.Analysis.Complex
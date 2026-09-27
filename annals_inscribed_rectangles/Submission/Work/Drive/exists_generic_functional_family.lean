import Mathlib
import Submission.Work.Drive.generic_regularization_gen
import Submission.Work.Drive.linearPlaneChart


/-!
# A generic linear functional for a finite family of smooth curves in `ℝ³`

Given finitely many `C^∞` curves `V i : ℝ → Eucl 3` which do not vanish on `[0,1]`, there is a
nonzero linear functional `ℓ` such that for every `i` the function `s ↦ ℓ (V i s)` does not vanish
at `s = 0` and has only *simple* zeros on `[0,1]` (in particular finitely many of them).

The proof runs the workspace's parametric Sard theorem `Work.Drive.generic_regularization_gen`
in dimension `m = 4`, `n = 1`: the parameter is the functional (identified with a vector of
`Eucl 3 = ℝ⁴` via `inner`), the `z`-variable is the pair `(time, dummy)` in `Amb 1 = ℝ²`, and the
family map is `Φ o x = (x.1 (V o (z 0))) • u`.  Two features of the Sard conclusion are used:

* at a zero the `z`-derivative is onto `ℝ¹`, which for this family means that the scalar derivative
  `s ↦ x.1 (V o s)` does not vanish at the zero;
* at a zero with `z 0 ∈ {0,1}` the restriction of the `z`-derivative to `{z 0 = 0}` is onto `ℝ¹`,
  which is *impossible* for this family (the derivative factors through the first coordinate), so
  the functional cannot vanish at time `0`.

An extra constant curve is added as the index `none` of `Option ι`; it produces a zero-free family
member, which forces the chosen functional to be nonzero (and handles the empty index type).
-/

namespace Work.Drive

open Set Filter
open scoped ContDiff Topology Filter

noncomputable section

/-! ## Generic linear functionals for a finite family of smooth curves in `ℝ³` -/

/-- The coordinate functional `z ↦ z 0` on the parameter plane `Amb 1 = ℝ²`. -/
def gfamCoord : Work.Drive.Amb 1 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0

@[simp] lemma gfamCoord_apply (z : Work.Drive.Amb 1) : gfamCoord z = z 0 :=
  PiLp.proj_apply 2 (fun _ : Fin 2 => ℝ) 0 z

lemma gfamCoord_surjective : Function.Surjective gfamCoord := fun s =>
  ⟨PiLp.single 2 (0 : Fin 2) s, by rw [gfamCoord_apply, PiLp.single_eq_same]⟩

/-- The basis vector of the one-dimensional target `Tgt 1 = ℝ¹`. -/
def gfamU : Work.Drive.Tgt 1 := PiLp.single 2 (0 : Fin 1) (1 : ℝ)

@[simp] lemma gfamU_apply_zero : (gfamU : Work.Drive.Tgt 1) 0 = 1 := PiLp.single_eq_same 2 0 1

lemma gfamU_ne_zero : gfamU ≠ 0 := by
  intro h
  have h1 : (gfamU : Work.Drive.Tgt 1) 0 = (0 : Work.Drive.Tgt 1) 0 := by rw [h]
  simp only [gfamU_apply_zero] at h1
  exact one_ne_zero h1

lemma gfam_smul_U (w : Work.Drive.Tgt 1) : (w 0) • gfamU = w := by
  apply WithLp.ofLp_injective 2
  funext i
  fin_cases i
  simp [PiLp.smul_apply, gfamU]

/-- The fixed reference vector of `ℝ⁴ = Eucl 3`. -/
def gfamRef : Eucl 3 := PiLp.single 2 (0 : Fin 4) (1 : ℝ)

lemma gfamRef_ne_zero : gfamRef ≠ 0 := by
  intro h
  have h1 : (gfamRef : Eucl 3) 0 = (0 : Eucl 3) 0 := by rw [h]
  simp only [gfamRef, PiLp.single_eq_same] at h1
  exact one_ne_zero h1

/-- The extended family: a fixed constant curve as the `none` index. -/
def gfamExtend {ι : Type*} (V : ι → ℝ → Eucl 3) : Option ι → ℝ → Eucl 3 :=
  fun o => Option.elim o (fun _ => gfamRef) V

/-- The family map handed to the parametric Sard theorem: it evaluates the functional `x.1` on the
curve `gfamExtend V o` at the parameter `gfamCoord x.2`. -/
def gfamPhi {ι : Type*} (V : ι → ℝ → Eucl 3) (o : Option ι) :
    Eucl 3 × Work.Drive.Amb 1 → Work.Drive.Tgt 1 :=
  fun x => (inner ℝ x.1 (gfamExtend V o (gfamCoord x.2))) • gfamU

lemma gfamExtend_contDiff {ι : Type*} (V : ι → ℝ → Eucl 3)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (o : Option ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gfamExtend V o) := by
  cases o with
  | none => exact contDiff_const
  | some i => exact hV i

lemma gfamPhi_contDiff {ι : Type*} (V : ι → ℝ → Eucl 3)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (o : Option ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (gfamPhi V o) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Eucl 3 × Work.Drive.Amb 1 =>
        inner ℝ x.1 (gfamExtend V o (gfamCoord x.2))) :=
    ContDiff.inner ℝ contDiff_fst
      ((gfamExtend_contDiff V hV o).comp (gfamCoord.contDiff.comp contDiff_snd))
  exact h1.smul_const gfamU

/-- The parameter-derivative of `gfamPhi V o` in the functional variable. -/
lemma gfamPhi_hasFDerivAt_fst {ι : Type*} (V : ι → ℝ → Eucl 3) (o : Option ι) (p : Eucl 3)
    (z : Work.Drive.Amb 1) :
    HasFDerivAt (fun p' : Eucl 3 => gfamPhi V o (p', z))
      ((innerSL ℝ (gfamExtend V o (gfamCoord z))).smulRight gfamU) p := by
  have hfun : (fun p' : Eucl 3 => gfamPhi V o (p', z))
      = ⇑((innerSL ℝ (gfamExtend V o (gfamCoord z))).smulRight gfamU) := by
    funext p'
    simp only [gfamPhi, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [real_inner_comm]
  rw [hfun]
  exact ContinuousLinearMap.hasFDerivAt _

/-- The parameter-derivative of `gfamPhi V o` in the `z`-variable. -/
lemma gfamPhi_hasFDerivAt_snd {ι : Type*} (V : ι → ℝ → Eucl 3)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (o : Option ι) (p : Eucl 3)
    (z : Work.Drive.Amb 1) :
    HasFDerivAt (fun z' : Work.Drive.Amb 1 => gfamPhi V o (p, z'))
      (((fderiv ℝ (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z)).smulRight gfamU).comp
        gfamCoord) z := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => inner ℝ p (gfamExtend V o s)) :=
    ContDiff.inner ℝ contDiff_const (gfamExtend_contDiff V hV o)
  have hdiff : DifferentiableAt ℝ (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z) :=
    (hc.differentiable (by simp)).differentiableAt
  have h1 : HasFDerivAt (fun s : ℝ => (inner ℝ p (gfamExtend V o s)) • gfamU)
      ((fderiv ℝ (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z)).smulRight gfamU)
      (gfamCoord z) := hdiff.hasFDerivAt.smul_const gfamU
  have h2 := h1.comp z (ContinuousLinearMap.hasFDerivAt gfamCoord)
  simpa only [Function.comp_def, gfamPhi] using h2

lemma gfam_smulRight_surjective {c : Eucl 3} (hc : c ≠ 0) :
    Function.Surjective ((innerSL ℝ c).smulRight gfamU) := by
  intro w
  have hcc : inner ℝ c c ≠ 0 := inner_self_ne_zero.mpr hc
  refine ⟨(w 0 / inner ℝ c c) • c, ?_⟩
  rw [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_right,
    div_mul_cancel₀ _ hcc, gfam_smul_U]

/-- The `z`-derivative is never surjective at a point of the face `z 0 = 0`; consequently the
functional cannot vanish at the initial time. -/
lemma gfamPhi_face_zero {ι : Type*} (V : ι → ℝ → Eucl 3)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (o : Option ι) {p : Eucl 3}
    (hface : ∀ z : Work.Drive.Amb 1, z ∈ Submission.Drive.unitBox 1 → gfamPhi V o (p, z) = 0 →
      (z 0 = 0 ∨ z 0 = 1) →
      Function.Surjective (fun v : {v : Work.Drive.Amb 1 // v 0 = 0} =>
        fderiv ℝ (fun z' : Work.Drive.Amb 1 => gfamPhi V o (p, z')) z v.1)) :
    inner ℝ p (gfamExtend V o 0) ≠ 0 := by
  intro habs
  have hz0 : (0 : Work.Drive.Amb 1) ∈ Submission.Drive.unitBox 1 := by intro j; simp
  have hc0 : gfamCoord (0 : Work.Drive.Amb 1) = 0 := by simp [gfamCoord_apply]
  have h0 : gfamPhi V o (p, (0 : Work.Drive.Amb 1)) = 0 := by
    simp only [gfamPhi, hc0, habs, zero_smul]
  have hfaceo := hface 0 hz0 h0 (Or.inl rfl)
  have hfd := gfamPhi_hasFDerivAt_snd V hV o p (0 : Work.Drive.Amb 1)
  have hzero : ∀ v : {v : Work.Drive.Amb 1 // v 0 = 0},
      (fderiv ℝ (fun z' : Work.Drive.Amb 1 => gfamPhi V o (p, z'))
        (0 : Work.Drive.Amb 1)) v.1 = 0 := by
    intro v
    have hv0 : gfamCoord v.1 = 0 := by rw [gfamCoord_apply, v.2]
    rw [hfd.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, hv0,
      map_zero, zero_smul]
  obtain ⟨v, hv⟩ := hfaceo gfamU
  have hv' : (fderiv ℝ (fun z' : Work.Drive.Amb 1 => gfamPhi V o (p, z'))
      (0 : Work.Drive.Amb 1)) v.1 = gfamU := hv
  rw [hzero v] at hv'
  exact gfamU_ne_zero hv'.symm

/-- A linear functional `ℝ → ℝ` vanishing at `1` is zero. -/
lemma realCLM_eq_zero_of_apply_one_eq_zero (L : ℝ →L[ℝ] ℝ) (h : L 1 = 0) : L = 0 := by
  refine ContinuousLinearMap.ext fun s => ?_
  show L s = 0
  calc L s = L (s • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = s • L 1 := map_smul L s 1
    _ = 0 := by rw [h, smul_zero]

/-- Surjectivity of the `z`-derivative at a zero forces the scalar derivative to be nonzero. -/
lemma gfam_deriv_ne_zero {ι : Type*} (V : ι → ℝ → Eucl 3)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i)) (o : Option ι) {p : Eucl 3}
    {z : Work.Drive.Amb 1}
    (h : Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb 1 => gfamPhi V o (p, z')) z)) :
    deriv (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z) ≠ 0 := by
  have hfd := gfamPhi_hasFDerivAt_snd V hV o p z
  rw [hfd.fderiv] at h
  have h' : Function.Surjective (fun x : Work.Drive.Amb 1 =>
      ((fderiv ℝ (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z)).smulRight gfamU)
        (gfamCoord x)) := by
    intro w
    obtain ⟨x, hx⟩ := h w
    exact ⟨x, by rw [ContinuousLinearMap.comp_apply] at hx; exact hx⟩
  have hsurj := (Function.Surjective.of_comp_iff _ gfamCoord_surjective).mp h'
  have hLne : fderiv ℝ (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z) ≠ 0 := by
    intro h0
    rw [h0, ContinuousLinearMap.zero_smulRight] at hsurj
    obtain ⟨v, hv⟩ := hsurj gfamU
    exact gfamU_ne_zero hv.symm
  intro hderiv
  have hL1 : fderiv ℝ (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z) 1
      = deriv (fun s : ℝ => inner ℝ p (gfamExtend V o s)) (gfamCoord z) := by
    have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => inner ℝ p (gfamExtend V o s)) :=
      ContDiff.inner ℝ contDiff_const (gfamExtend_contDiff V hV o)
    exact (((hc.differentiable (by simp)).differentiableAt).hasFDerivAt.hasDerivAt).deriv
  exact hLne (realCLM_eq_zero_of_apply_one_eq_zero _ (by rw [hL1, hderiv]))

/-- Near a point with nonzero derivative, a differentiable function takes each value at most once. -/
lemma gfam_slope_ne_zero {g : ℝ → ℝ} {t : ℝ} (h : HasDerivAt g (deriv g t) t)
    (hne : deriv g t ≠ 0) : ∃ ε > 0, ∀ s, |s - t| < ε → s ≠ t → g s ≠ g t := by
  have hlim : ∀ᶠ s in 𝓝[≠] t, slope g t s ≠ 0 :=
    h.tendsto_slope.eventually (eventually_ne_nhds hne)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hlim
  refine ⟨ε, hε, fun s hs hst hgs => ?_⟩
  have hmem : s ∈ Metric.ball t ε ∩ {t}ᶜ := ⟨by rw [Metric.mem_ball, Real.dist_eq]; exact hs, hst⟩
  have hne' : slope g t s ≠ 0 := hsub hmem
  apply hne'
  have hsl : slope g t s = (s - t)⁻¹ • (g s - g t) := rfl
  rw [hsl, hgs, sub_self, smul_zero]

/-- A function whose zeros in `[0,1]` are all simple has finitely many of them. -/
lemma gfam_zeroSet_finite {g : ℝ → ℝ} (hgd : ∀ t, HasDerivAt g (deriv g t) t)
    (hne : ∀ t ∈ Icc (0 : ℝ) 1, g t = 0 → deriv g t ≠ 0) :
    {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ g t = 0}.Finite := by
  classical
  have hgcont : Continuous g := continuous_iff_continuousAt.mpr fun t => (hgd t).continuousAt
  have hSclosed : IsClosed {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ g t = 0} :=
    isClosed_Icc.inter (isClosed_eq hgcont continuous_const)
  have hScomp : IsCompact {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ g t = 0} :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed fun t ht => ht.1
  have hisol : ∀ t : {t : ℝ // t ∈ Icc (0 : ℝ) 1 ∧ g t = 0},
      ∃ ε > 0, ∀ s, |s - t.1| < ε → s ≠ t.1 → g s ≠ g t.1 :=
    fun t => gfam_slope_ne_zero (hgd t.1) (hne t.1 t.2.1 t.2.2)
  choose ε hεpos hisol' using hisol
  obtain ⟨T, hT⟩ := hScomp.elim_finite_subcover
    (fun t : {t : ℝ // t ∈ Icc (0 : ℝ) 1 ∧ g t = 0} => Ioo (t.1 - ε t) (t.1 + ε t))
    (fun _ => isOpen_Ioo)
    (fun t ht => mem_iUnion.mpr ⟨⟨t, ht⟩, by
      refine ⟨?_, ?_⟩ <;> linarith [hεpos ⟨t, ht⟩]⟩)
  have hsub : {t : ℝ | t ∈ Icc (0 : ℝ) 1 ∧ g t = 0} ⊆ (T.image Subtype.val : Finset ℝ) := by
    intro t ht
    obtain ⟨t', ht'T, ht'⟩ := mem_iUnion₂.mp (hT ht)
    have hthis : t = t'.1 := by
      by_contra hne'
      refine hisol' t' t ?_ hne' (by rw [ht.2, t'.2.2])
      rw [abs_lt]
      exact ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
    rw [hthis]
    exact Finset.mem_image.mpr ⟨t', ht'T, rfl⟩
  exact Set.Finite.subset (T.image Subtype.val).finite_toSet hsub

/-- The first-coordinate curve is an element of the unit box `[0,1]²`. -/
lemma gfam_single_mem_unitBox {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    PiLp.single 2 (0 : Fin 2) t ∈ Submission.Drive.unitBox 1 := by
  intro j
  rw [PiLp.single_apply]
  split_ifs with h
  · exact ht
  · exact ⟨le_rfl, zero_le_one⟩

/-- **Every finite family of smooth nonvanishing curves admits a linear functional whose
restrictions to the curves have only simple zeros on `[0,1]` and do not vanish at time `0`.** -/
theorem exists_generic_functional_family (ι : Type*) [Fintype ι] (V : ι → ℝ → Eucl 3)
    (hV : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (V i))
    (hVne : ∀ i t, t ∈ Set.Icc (0 : ℝ) 1 → V i t ≠ 0) :
    ∃ ℓ : Eucl 3 →L[ℝ] ℝ, ℓ ≠ 0 ∧
      (∀ i : ι, ℓ (V i 0) ≠ 0 ∧
        ({t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ ℓ (V i t) = 0}).Finite ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, ℓ (V i t) = 0 →
          deriv (fun s : ℝ => ℓ (V i s)) t ≠ 0)) := by
  classical
  obtain ⟨p, -, hmain, hface⟩ :=
    generic_regularization_gen 4 1 (Option ι) 1 one_pos (gfamPhi V)
      (fun o => gfamPhi_contDiff V hV o)
      (fun o q z hz _ => by
        have hcne : gfamExtend V o (gfamCoord z) ≠ 0 := by
          cases o with
          | none => exact gfamRef_ne_zero
          | some i => exact hVne i (gfamCoord z) (by rw [gfamCoord_apply]; exact hz 0)
        rw [(gfamPhi_hasFDerivAt_fst V o q z).fderiv]
        exact gfam_smulRight_surjective hcne)
  have hface0 : ∀ o : Option ι, ∀ z : Work.Drive.Amb 1, z ∈ Submission.Drive.unitBox 1 →
      gfamPhi V o (p, z) = 0 → (z 0 = 0 ∨ z 0 = 1) →
      Function.Surjective (fun v : {v : Work.Drive.Amb 1 // v 0 = 0} =>
        fderiv ℝ (fun z' : Work.Drive.Amb 1 => gfamPhi V o (p, z')) z v.1) :=
    fun o z hz h0 hz0 => hface o 0 z hz h0 hz0
  have hzero0 : ∀ o : Option ι, inner ℝ p (gfamExtend V o 0) ≠ 0 :=
    fun o => gfamPhi_face_zero V hV o (hface0 o)
  refine ⟨innerSL ℝ p, ?_, ?_⟩
  · intro hzero
    have h : (innerSL ℝ p) gfamRef = 0 := by rw [hzero]; rfl
    rw [innerSL_apply_apply] at h
    refine hzero0 none ?_
    have he : gfamExtend V none (0 : ℝ) = gfamRef := by simp [gfamExtend]
    rw [he]
    exact h
  · intro i
    have he : gfamExtend V (some i) = V i := by
      funext s
      simp [gfamExtend]
    have hev : (fun s : ℝ => inner ℝ p (gfamExtend V (some i) s))
        = fun s : ℝ => inner ℝ p (V i s) :=
      congrArg (fun f : ℝ → Eucl 3 => fun s => inner ℝ p (f s)) he
    refine ⟨?_, ?_, ?_⟩
    · have h := hzero0 (some i)
      rw [congrArg (fun f : ℝ → Eucl 3 => f 0) he] at h
      rwa [innerSL_apply_apply]
    · have hgd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => inner ℝ p (V i s))
          (deriv (fun s : ℝ => inner ℝ p (V i s)) t) t := by
        intro t
        have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => inner ℝ p (V i s)) :=
          ContDiff.inner ℝ contDiff_const (hV i)
        exact ((hc.differentiable (by simp)).differentiableAt).hasDerivAt
      have hne : ∀ t ∈ Icc (0 : ℝ) 1, inner ℝ p (V i t) = 0 →
          deriv (fun s : ℝ => inner ℝ p (V i s)) t ≠ 0 := by
        intro t ht h0
        have hct : gfamCoord (PiLp.single 2 (0 : Fin 2) t) = t := by
          rw [gfamCoord_apply, PiLp.single_eq_same]
        have hpt : gfamPhi V (some i) (p, PiLp.single 2 (0 : Fin 2) t) = 0 := by
          have hf : gfamPhi V (some i) (p, PiLp.single 2 (0 : Fin 2) t)
              = (inner ℝ p (V i t)) • gfamU := by
            simp only [gfamPhi, gfamExtend, Option.elim_some, hct]
          rw [hf, h0, zero_smul]
        have h := gfam_deriv_ne_zero V hV (some i)
          (hmain (some i) _ (gfam_single_mem_unitBox ht) hpt)
        rw [hct, hev] at h
        exact h
      have hfin := gfam_zeroSet_finite hgd hne
      simpa only [innerSL_apply_apply] using hfin
    · intro t ht hzt
      have h0 : inner ℝ p (V i t) = 0 := by simpa only [innerSL_apply_apply] using hzt
      have hct : gfamCoord (PiLp.single 2 (0 : Fin 2) t) = t := by
        rw [gfamCoord_apply, PiLp.single_eq_same]
      have hpt : gfamPhi V (some i) (p, PiLp.single 2 (0 : Fin 2) t) = 0 := by
        have hf : gfamPhi V (some i) (p, PiLp.single 2 (0 : Fin 2) t)
            = (inner ℝ p (V i t)) • gfamU := by
          simp only [gfamPhi, gfamExtend, Option.elim_some, hct]
        rw [hf, h0, zero_smul]
      have h := gfam_deriv_ne_zero V hV (some i)
        (hmain (some i) _ (gfam_single_mem_unitBox ht) hpt)
      rw [hct, hev] at h
      have hfun : (fun s : ℝ => (innerSL ℝ p) (V i s)) = fun s : ℝ => inner ℝ p (V i s) := by
        funext s
        rw [innerSL_apply_apply]
      rw [hfun]
      exact h

end

end Work.Drive

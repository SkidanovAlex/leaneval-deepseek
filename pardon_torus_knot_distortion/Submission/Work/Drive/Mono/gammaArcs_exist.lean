
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.finite_zeroSet_of_isInvertible_fderiv

/-!
# The box trace near the cutting plane is a finite family of `C³` arcs

`Work.Drive.Mono.gammaArcs_exist` proves that, near a cutting level `u` at which the two faces
`i ≠ 2` cross the flat plane `{y (σ 2) = c (σ 2) + u}` regularly on the surface
(`Work.Drive.Mono.FaceCrossReg`), the trace `Γ = F ∩ {boxNorm c σ = s}` inside a band of the
plane is a finite union of arcs, each parametrised `C³`-ly **by the height** `y (σ 2)`, and that
every carrier point of the band with `boxNorm c σ = s` lies on one of them.

The proof has four layers.

* **The local model of a fibre (`exists_arcData`).**  Let `Ψ : ℝ × ℝ → ℝ × ℝ` be `C³` at `p₀` with
  invertible derivative and `Ψ p₀ = (a, v)`.  The inverse function theorem gives a local inverse
  `LI` of `Ψ` at `p₀`, which is `C³` there; the curve `β t = LI (a, v + t)` is `C³` near `0`, lies
  on the fibre `{Ψ = (a, v + t)}` (right inverse), and inverts `Ψ` on a neighbourhood `U ∋ p₀`
  (left inverse).  This is the only analytic input; everything else is bookkeeping.
* **A compactness cover (`exists_window_cover`).**  If the fibre of `(g, f)` over `(a, v)` inside a
  compact `K` lies in an open set `U`, then the points of `K ∩ {g = a}` whose `f`-value is close
  enough to `v` lie in `U` (a limiting argument: a sequence of counterexamples converges in `K` to
  a point of the fibre, hence into `U`, contradicting openness only eventually).
* **The crossing sets are finite (`crossSet_finite`).**  In the parameter plane the face curve of
  `(i, ε)` crosses the plane at the zero set of `q ↦ facePairMap ψ σ i q - (a, v)`, whose
  derivative is invertible at every zero of the fundamental domain `[0, 2π]²` by `FaceCrossReg`;
  `Work.Drive.Mono.finite_zeroSet_of_isInvertible_fderiv` gives finiteness.  The crossing
  parameters are collected in `branchFinset` (over the faces `i ∈ {0, 1}`, `ε = ±1`), each carrying
  its local model `arcDatum`.
* **Assembly.**  The cover of each face (`hcover` in the proof) is applied at the face which the
  point `z` of the statement is tight on; the strict margin `|u| < boxSide 2 * s` removes the
  horizontal faces (a point with `|z (σ 2) - c (σ 2)| = boxSide 2 * s` is at distance at least
  `boxSide 2 * s - |u| > 0` from the cutting plane), and reducing a parameter modulo `2π` puts it
  in the fundamental domain.  Note that the hypothesis of the last clause excluding the
  "both-extremal" points is not needed: the arcs cover those too.

The result is sorry-free and axiom-clean.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set Filter
open scoped ENNReal _root_.Topology

namespace Work.Drive.Mono

noncomputable section

/-! ## Part A: the local height parametrisation at a regular crossing point

Let `Ψ : ℝ × ℝ → ℝ × ℝ` be `C³` at `p₀` with invertible derivative there and `Ψ p₀ = (a, v)`.  The
fibre `{Ψ = (a, v + t)}` near `p₀` is, for `t` near `0`, the image of a single `C³` curve `β` with
`β t` the unique preimage of `(a, v + t)` close to `p₀`.  Everything is read off the inverse
function theorem: `β t = LI (a, v + t)` with `LI` the local inverse of `Ψ` at `p₀`. -/

/-- **The local parametrisation of a fibre of a regular point, by the second coordinate.** -/
private theorem exists_arcData {Ψ : ℝ × ℝ → ℝ × ℝ} {p₀ : ℝ × ℝ} {a v : ℝ}
    (hΨ : ContDiffAt ℝ 3 Ψ p₀) (hp₀ : Ψ p₀ = (a, v))
    (hinv : (fderiv ℝ Ψ p₀).IsInvertible) :
    ∃ (β : ℝ → ℝ × ℝ) (U : Set (ℝ × ℝ)) (θ : ℝ),
      0 < θ ∧ U ∈ 𝓝 p₀ ∧ IsOpen U ∧ ContDiffOn ℝ 3 β (Set.Icc (-θ) θ) ∧ β 0 = p₀ ∧
      (∀ t ∈ Set.Icc (-θ) θ, Ψ (β t) = (a, v + t)) ∧
      (∀ q ∈ U, (Ψ q).1 = a → β ((Ψ q).2 - v) = q) := by
  classical
  obtain ⟨A, hA⟩ := hinv
  have hn : (3 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hderivF : HasFDerivAt Ψ (fderiv ℝ Ψ p₀) p₀ := (hΨ.differentiableAt hn).hasFDerivAt
  have hderiv : HasFDerivAt Ψ (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p₀ :=
    hderivF.congr_fderiv hA.symm
  have hssd : HasStrictFDerivAt Ψ (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p₀ :=
    hΨ.hasStrictFDerivAt' hderiv hn
  let LI : ℝ × ℝ → ℝ × ℝ := hΨ.localInverse hderiv hn
  have hLIcont : ContDiffAt ℝ 3 LI (a, v) := by
    have h := hΨ.to_localInverse hderiv hn
    rwa [hp₀] at h
  let β : ℝ → ℝ × ℝ := fun t => LI (a, v + t)
  have hβ0 : β 0 = p₀ := by
    show LI (a, v + 0) = p₀
    rw [add_zero, ← hp₀]
    exact hΨ.localInverse_apply_image hderiv hn
  have hleft_ev : ∀ᶠ q in 𝓝 p₀, (Ψ q).1 = a → β ((Ψ q).2 - v) = q := by
    filter_upwards [hssd.eventually_left_inverse] with q hq hqa
    have harg : ((a : ℝ), v + ((Ψ q).2 - v)) = Ψ q := by
      rw [show v + ((Ψ q).2 - v) = (Ψ q).2 by ring]
      exact Prod.ext hqa.symm rfl
    show LI (a, v + ((Ψ q).2 - v)) = q
    rw [harg]
    exact hq
  have hright_ev : ∀ᶠ t in 𝓝 (0 : ℝ), Ψ (β t) = (a, v + t) := by
    have hφ : Tendsto (fun t : ℝ => ((a : ℝ), v + t)) (𝓝 0) (𝓝 (a, v)) := by
      have hc : Continuous fun t : ℝ => ((a : ℝ), v + t) :=
        continuous_const.prodMk (continuous_const.add continuous_id)
      simpa [ContinuousAt] using hc.continuousAt (x := (0 : ℝ))
    have h' : ∀ᶠ y in 𝓝 (a, v), Ψ (LI y) = y := by
      have h2 := hssd.eventually_right_inverse
      rwa [hp₀] at h2
    simpa [β] using hφ.eventually h'
  -- an open neighbourhood of `(a, v)` on which `LI` is `C³`
  have hLI3ev : ∀ᶠ y in 𝓝 (a, v), ContDiffAt ℝ 3 LI y :=
    hLIcont.eventually (by norm_num : (3 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞))
  obtain ⟨W, hWmem, hWsub⟩ := hLI3ev.exists_mem
  obtain ⟨W', hW'sub, hW'open, hW'mem⟩ := mem_nhds_iff.mp hWmem
  have hcont_a : Continuous fun t : ℝ => ((a : ℝ), v + t) :=
    continuous_const.prodMk (continuous_const.add continuous_id)
  have hW'mem' : ((a : ℝ), v + 0) ∈ W' := by simpa using hW'mem
  have hpre : {t : ℝ | ((a : ℝ), v + t) ∈ W'} ∈ 𝓝 (0 : ℝ) :=
    hcont_a.continuousAt.preimage_mem_nhds (hW'open.mem_nhds hW'mem')
  obtain ⟨θ₁, hθ₁, hθ₁sub⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨θ₂, hθ₂, hθ₂sub⟩ := Metric.mem_nhds_iff.mp hright_ev
  have hθpos : 0 < min θ₁ θ₂ / 2 := by positivity
  -- the left-inverse neighbourhood of `p₀`, made open
  obtain ⟨U₀, hU₀mem, hU₀sub⟩ := hleft_ev.exists_mem
  obtain ⟨U, hUsub, hUopen, hUmem⟩ := mem_nhds_iff.mp hU₀mem
  refine ⟨β, U, min θ₁ θ₂ / 2, hθpos, hUopen.mem_nhds hUmem, hUopen, ?_, hβ0, ?_, ?_⟩
  · intro t ht
    have ht1 : t ∈ Metric.ball (0 : ℝ) θ₁ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1, min_le_left θ₁ θ₂], by linarith [ht.2, min_le_left θ₁ θ₂]⟩
    have hcomp : ContDiffAt ℝ 3 (fun s : ℝ => LI (((a : ℝ), v + s))) t :=
      ContDiffAt.comp t (hWsub ((a : ℝ), v + t) (hW'sub (hθ₁sub ht1)))
        (contDiffAt_const.prodMk (contDiffAt_const.add contDiffAt_id))
    exact hcomp.contDiffWithinAt
  · intro t ht
    have ht2 : t ∈ Metric.ball (0 : ℝ) θ₂ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1, min_le_right θ₁ θ₂], by linarith [ht.2, min_le_right θ₁ θ₂]⟩
    exact hθ₂sub ht2
  · intro q hq hqa
    exact hU₀sub q (hUsub hq) hqa

/-- The same statement with the parametrisation packaged as a triple, for the `if`-definition
below. -/
private theorem exists_arcDatum {Ψ : ℝ × ℝ → ℝ × ℝ} {p₀ : ℝ × ℝ} {a v : ℝ}
    (hΨ : ContDiffAt ℝ 3 Ψ p₀) (hp₀ : Ψ p₀ = (a, v))
    (hinv : (fderiv ℝ Ψ p₀).IsInvertible) :
    ∃ d : (ℝ → ℝ × ℝ) × Set (ℝ × ℝ) × ℝ,
      0 < d.2.2 ∧ d.2.1 ∈ 𝓝 p₀ ∧ IsOpen d.2.1 ∧
      ContDiffOn ℝ 3 d.1 (Set.Icc (-d.2.2) d.2.2) ∧ d.1 0 = p₀ ∧
      (∀ t ∈ Set.Icc (-d.2.2) d.2.2, Ψ (d.1 t) = (a, v + t)) ∧
      (∀ q ∈ d.2.1, (Ψ q).1 = a → d.1 ((Ψ q).2 - v) = q) := by
  obtain ⟨β, U, θ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_arcData hΨ hp₀ hinv
  exact ⟨(β, U, θ), h1, h2, h3, h4, h5, h6, h7⟩

/-- **A compactness cover with a height window.**  If `K` is compact and the zero set of `f - v` on
`K ∩ {g = a}` is contained in an open set `U`, then every point of `K ∩ {g = a}` whose `f`-value is
close enough to `v` lies in `U`. -/
private theorem exists_window_cover {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    {g f : ℝ × ℝ → ℝ} (hg : Continuous g) (hf : Continuous f) {a v : ℝ} {U : Set (ℝ × ℝ)}
    (hUo : IsOpen U) (hCU : ∀ p ∈ K, g p = a → f p = v → p ∈ U) :
    ∃ η > 0, ∀ p ∈ K, g p = a → |f p - v| ≤ η → p ∈ U := by
  by_contra h
  push Not at h
  have hseq : ∀ n : ℕ, ∃ p, p ∈ K ∧ g p = a ∧ |f p - v| ≤ 1 / (n + 1) ∧ p ∉ U :=
    fun n => h _ (by positivity)
  choose p hp using hseq
  obtain ⟨z, hzK, φ, hφmono, hφtend⟩ := hK.tendsto_subseq (fun n => (hp n).1)
  have hgz : g z = a := by
    refine tendsto_nhds_unique ((hg.tendsto z).comp hφtend) ?_
    exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => ((hp (φ n)).2.1).symm)
  have hfv : f z = v := by
    have h1 : Tendsto (fun n => f (p (φ n))) atTop (𝓝 (f z)) := (hf.tendsto z).comp hφtend
    have habs : Tendsto (fun n => |f (p (φ n)) - v|) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => (hp (φ n)).2.2.1) ?_
      have hnn : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [Function.comp_def] using hnn.comp hφmono.tendsto_atTop
    have h2 : Tendsto (fun n => f (p (φ n)) - v) atTop (𝓝 0) :=
      (tendsto_zero_iff_abs_tendsto_zero (l := atTop) (fun n => f (p (φ n)) - v)).mpr habs
    have h3 : Tendsto (fun n => f (p (φ n))) atTop (𝓝 v) := by
      have h4 := h2.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v))
      simpa using h4
    exact tendsto_nhds_unique h1 h3
  have hzU : z ∈ U := hCU z hzK hgz hfv
  have hev : ∀ᶠ n in atTop, p (φ n) ∈ U := hφtend.eventually (hUo.mem_nhds hzU)
  obtain ⟨n, hn⟩ := hev.exists
  exact (hp (φ n)).2.2.2 hn

/-! ## Part B: the geometry of the box sphere and the crossing sets -/

/-- The fundamental domain `[0, 2π]²` of the parameter plane. -/
def arcFundBox : Set (ℝ × ℝ) := Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)

theorem mem_arcFundBox {p : ℝ × ℝ} :
    p ∈ arcFundBox ↔ p.1 ∈ Set.Icc 0 (2 * Real.pi) ∧ p.2 ∈ Set.Icc 0 (2 * Real.pi) :=
  Iff.rfl

/-- The pair map of the face `i`: `q ↦ (y_{σ i}, y_{σ 2}) (par ψ q)`. -/
def facePairMap (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ℝ × ℝ → ℝ × ℝ :=
  fun q => ((Work.BoxShrink.Pinch.par ψ q) (σ i), (Work.BoxShrink.Pinch.par ψ q) (σ 2))

theorem facePairMap_contDiff (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3) :
    ContDiff ℝ 3 (facePairMap ψ σ i) := by
  have hpar : ContDiff ℝ 3 (Work.BoxShrink.Pinch.par ψ) :=
    (Work.BoxShrink.Pinch.par_contDiff ψ).of_le (by decide)
  have hproj (j : Fin 3) :
      ContDiff ℝ 3 (fun q : ℝ × ℝ => (Work.BoxShrink.Pinch.par ψ q) (σ j)) := by
    have h1 : ContDiff ℝ 3 (fun q : ℝ × ℝ =>
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (σ j)) (Work.BoxShrink.Pinch.par ψ q)) :=
      (ContinuousLinearMap.contDiff
        (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (σ j))).comp hpar
    simpa [Function.comp_def] using h1
  exact (hproj i).prodMk (hproj 2)

theorem facePairMap_contDiffAt (ψ : Submission.Diffeo) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (p : ℝ × ℝ) : ContDiffAt ℝ 3 (facePairMap ψ σ i) p :=
  (facePairMap_contDiff ψ σ i).contDiffAt

/-- The crossing set of the face `(i, ε)` with the cutting plane. -/
def crossSet (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (i : Fin 3)
    (ε : ℝ) : Set (ℝ × ℝ) :=
  {p | p ∈ arcFundBox ∧ facePairMap ψ σ i p =
    (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u)}

theorem mem_crossSet {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {i : Fin 3} {ε : ℝ} {p : ℝ × ℝ} :
    p ∈ crossSet ψ s u c σ i ε ↔ p ∈ arcFundBox ∧ facePairMap ψ σ i p =
      (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u) :=
  Iff.rfl

/-- The crossing set is finite when the face crosses the plane regularly. -/
theorem crossSet_finite (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (hi : i ≠ 2) (hε : ε = 1 ∨ ε = -1)
    (hX : FaceCrossReg ψ c σ s u) : (crossSet ψ s u c σ i ε).Finite := by
  classical
  set w : ℝ × ℝ := (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u) with hw
  have hK : IsCompact arcFundBox := isCompact_Icc.prod isCompact_Icc
  have hcd : ∀ x ∈ arcFundBox, ContDiffAt ℝ 1 (fun q => facePairMap ψ σ i q - w) x := by
    intro x _
    exact ((facePairMap_contDiff ψ σ i).contDiffAt.sub contDiffAt_const).of_le (by norm_num)
  have hinv : ∀ x ∈ arcFundBox, (fun q => facePairMap ψ σ i q - w) x = 0 →
      (fderiv ℝ (fun q => facePairMap ψ σ i q - w) x).IsInvertible := by
    intro x _ hx
    have hxw : facePairMap ψ σ i x = w := sub_eq_zero.mp hx
    obtain ⟨B, hB⟩ := hX i hi ε hε x (congrArg Prod.fst hxw) (congrArg Prod.snd hxw)
    refine ⟨B, ?_⟩
    rw [fderiv_sub_const w]
    exact hB
  have h := finite_zeroSet_of_isInvertible_fderiv hK hcd hinv
  have hset : crossSet ψ s u c σ i ε = arcFundBox ∩ (fun q => facePairMap ψ σ i q - w) ⁻¹' {0} := by
    ext p
    simp only [mem_crossSet, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      sub_eq_zero]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩
  rwa [hset]

/-- **A point of the surface on the box sphere is tight in some coordinate.** -/
theorem exists_face_eq_of_boxNorm_eq {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {z : R3}
    (hz : Submission.boxNorm c σ z = s) :
    ∃ i : Fin 3, |z (σ i) - c (σ i)| = Submission.boxSide i * s := by
  rw [Submission.boxNorm] at hz
  rcases max_eq_iff.mp hz with h | h
  · rcases max_eq_iff.mp h.1 with h1 | h1
    · refine ⟨0, ?_⟩
      rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos 0))] at h1
      rw [h1.1, mul_comm]
    · refine ⟨1, ?_⟩
      rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos 1))] at h1
      rw [h1.1, mul_comm]
  · refine ⟨2, ?_⟩
    rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos 2))] at h
    rw [h.1, mul_comm]

/-- **A parameter over a point of the surface can be taken in the fundamental domain.** -/
theorem exists_mem_arcFundBox_par_eq (ψ : Submission.Diffeo) {z : R3}
    (hz : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier) :
    ∃ p ∈ arcFundBox, Work.BoxShrink.Pinch.par ψ p = z := by
  obtain ⟨p₀, hp₀⟩ := hz
  simp only at hp₀
  rw [Work.Smooth.Morse.torus_psi] at hp₀
  have hp₀' : Work.BoxShrink.Pinch.par ψ p₀ = z := hp₀
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  set k : ℤ := ⌊p₀.1 / (2 * Real.pi)⌋ with hk
  set l : ℤ := ⌊p₀.2 / (2 * Real.pi)⌋ with hl
  have hklow : 0 ≤ p₀.1 - (k : ℝ) * (2 * Real.pi) := by
    have h1 : (k : ℝ) ≤ p₀.1 / (2 * Real.pi) := Int.floor_le _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h2pi)
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at h2
    linarith
  have hkhigh : p₀.1 - (k : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
    have h1 : p₀.1 / (2 * Real.pi) < (k : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 := mul_lt_mul_of_pos_right h1 h2pi
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi), add_mul, one_mul] at h2
    linarith
  have hllow : 0 ≤ p₀.2 - (l : ℝ) * (2 * Real.pi) := by
    have h1 : (l : ℝ) ≤ p₀.2 / (2 * Real.pi) := Int.floor_le _
    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt h2pi)
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi)] at h2
    linarith
  have hlhigh : p₀.2 - (l : ℝ) * (2 * Real.pi) ≤ 2 * Real.pi := by
    have h1 : p₀.2 / (2 * Real.pi) < (l : ℝ) + 1 := Int.lt_floor_add_one _
    have h2 := mul_lt_mul_of_pos_right h1 h2pi
    rw [div_mul_cancel₀ _ (ne_of_gt h2pi), add_mul, one_mul] at h2
    linarith
  refine ⟨(p₀.1 - (k : ℝ) * (2 * Real.pi), p₀.2 - (l : ℝ) * (2 * Real.pi)),
    ⟨⟨hklow, hkhigh⟩, hllow, hlhigh⟩, ?_⟩
  rw [← hp₀']
  rw [← Work.BoxShrink.Pinch.par_period ψ p₀ (-k) (-l)]
  congr 1
  refine Prod.ext ?_ ?_ <;> push_cast <;> ring


/-! ## Part C: the crossing data and its enumeration -/

/-- A crossing parameter of a face of the box sphere with the cutting plane. -/
structure FaceBranch (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) where
  /-- the face -/
  i : Fin 3
  /-- the sign of the face -/
  ε : ℝ
  /-- the parameter -/
  p : ℝ × ℝ
  hi : i ≠ 2
  hε : ε = 1 ∨ ε = -1
  hmem : p ∈ arcFundBox
  hcross : facePairMap ψ σ i p = (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u)

/-- The local arc data at a crossing parameter: the parametrisation `β` by height, the
neighbourhood on which `β` inverts the pair map, and the radius on which the identities hold. -/
def arcDatum (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (p : ℝ × ℝ) : (ℝ → ℝ × ℝ) × Set (ℝ × ℝ) × ℝ := by
  classical
  exact if h : i ≠ 2 ∧ (ε = 1 ∨ ε = -1) ∧ facePairMap ψ σ i p =
        (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u) ∧
      (fderiv ℝ (facePairMap ψ σ i) p).IsInvertible
    then Classical.choose (exists_arcDatum (facePairMap_contDiffAt ψ σ i p) h.2.2.1 h.2.2.2)
    else (fun _ => 0, Set.univ, 1)

/-- The specification of `arcDatum` at a genuine crossing parameter. -/
theorem arcDatum_spec (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (p : ℝ × ℝ) (hi : i ≠ 2) (hε : ε = 1 ∨ ε = -1)
    (hp : facePairMap ψ σ i p = (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u))
    (hinv : (fderiv ℝ (facePairMap ψ σ i) p).IsInvertible) :
    0 < (arcDatum ψ s u c σ i ε p).2.2 ∧
    (arcDatum ψ s u c σ i ε p).2.1 ∈ 𝓝 p ∧
    IsOpen (arcDatum ψ s u c σ i ε p).2.1 ∧
    ContDiffOn ℝ 3 (arcDatum ψ s u c σ i ε p).1
      (Set.Icc (-(arcDatum ψ s u c σ i ε p).2.2) (arcDatum ψ s u c σ i ε p).2.2) ∧
    (arcDatum ψ s u c σ i ε p).1 0 = p ∧
    (∀ t ∈ Set.Icc (-(arcDatum ψ s u c σ i ε p).2.2) (arcDatum ψ s u c σ i ε p).2.2,
      facePairMap ψ σ i ((arcDatum ψ s u c σ i ε p).1 t) =
        (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u + t)) ∧
    (∀ q ∈ (arcDatum ψ s u c σ i ε p).2.1,
      (facePairMap ψ σ i q).1 = c (σ i) + ε * Submission.boxSide i * s →
      (arcDatum ψ s u c σ i ε p).1 ((facePairMap ψ σ i q).2 - (c (σ 2) + u)) = q) := by
  classical
  have hif : arcDatum ψ s u c σ i ε p =
      Classical.choose (exists_arcDatum (facePairMap_contDiffAt ψ σ i p) hp hinv) := by
    rw [arcDatum]
    exact dif_pos ⟨hi, hε, hp, hinv⟩
  rw [hif]
  exact Classical.choose_spec (exists_arcDatum (facePairMap_contDiffAt ψ σ i p) hp hinv)

/-- The crossing parameters of one face, as a finset of branches. -/
def crossFinset (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (i : Fin 3) (ε : ℝ) (hi : i ≠ 2) (hε : ε = 1 ∨ ε = -1)
    (hX : FaceCrossReg ψ c σ s u) : Finset (FaceBranch ψ s u c σ) := by
  classical
  exact ((crossSet_finite ψ s u c σ i ε hi hε hX).toFinset).attach.image fun p =>
    ⟨i, ε, p.val, hi, hε,
      (mem_crossSet.mp ((Set.Finite.mem_toFinset _).mp p.property)).1,
      (mem_crossSet.mp ((Set.Finite.mem_toFinset _).mp p.property)).2⟩

theorem mem_crossFinset {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {i : Fin 3} {ε : ℝ} {p : ℝ × ℝ} (hi : i ≠ 2) (hε : ε = 1 ∨ ε = -1)
    (hX : FaceCrossReg ψ c σ s u) (hp : p ∈ crossSet ψ s u c σ i ε) :
    (⟨i, ε, p, hi, hε, (mem_crossSet.mp hp).1, (mem_crossSet.mp hp).2⟩ :
        FaceBranch ψ s u c σ) ∈ crossFinset ψ s u c σ i ε hi hε hX := by
  classical
  rw [crossFinset]
  exact Finset.mem_image.mpr
    ⟨⟨p, (Set.Finite.mem_toFinset _).mpr hp⟩, Finset.mem_attach _ _, rfl⟩

/-- The pairs `(i, ε)` of faces which are not the horizontal one. -/
def branchPairs : Finset (Fin 3 × ℝ) :=
  (Finset.univ.filter (fun i : Fin 3 => i ≠ 2)) ×ˢ ({1, -1} : Finset ℝ)

theorem mem_branchPairs {i : Fin 3} {ε : ℝ} (hi : i ≠ 2) (hε : ε = 1 ∨ ε = -1) :
    (i, ε) ∈ branchPairs := by
  classical
  rw [branchPairs, Finset.mem_product]
  refine ⟨?_, ?_⟩
  · rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi⟩
  · rcases hε with h | h <;> simp [h]

/-- The finset of all crossing parameters over the four faces. -/
def branchFinset (ψ : Submission.Diffeo) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hX : FaceCrossReg ψ c σ s u) : Finset (FaceBranch ψ s u c σ) := by
  classical
  exact branchPairs.attach.biUnion fun q =>
    have h1 := (Finset.mem_product.mp q.property).1
    have h2 := (Finset.mem_product.mp q.property).2
    crossFinset ψ s u c σ q.val.1 q.val.2 (Finset.mem_filter.mp h1).2
      (by simp only [Finset.mem_insert, Finset.mem_singleton] at h2; exact h2) hX

theorem mem_branchFinset {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {hX : FaceCrossReg ψ c σ s u} {i : Fin 3} {ε : ℝ} {p : ℝ × ℝ} (hi : i ≠ 2)
    (hε : ε = 1 ∨ ε = -1) (hp : p ∈ crossSet ψ s u c σ i ε) :
    (⟨i, ε, p, hi, hε, (mem_crossSet.mp hp).1, (mem_crossSet.mp hp).2⟩ :
        FaceBranch ψ s u c σ) ∈ branchFinset ψ s u c σ hX := by
  classical
  rw [branchFinset]
  exact Finset.mem_biUnion.mpr
    ⟨⟨(i, ε), mem_branchPairs hi hε⟩, Finset.mem_attach _ _, mem_crossFinset hi hε hX hp⟩

/-! ## Part D: the arcs cover the band -/

set_option maxHeartbeats 800000 in
theorem gammaArcs_exist (ψ : Submission.Diffeo) {s u : ℝ} (hs : 0 < s) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (hu : |u| < Submission.boxSide 2 * s)
    (hX : Work.Drive.Mono.FaceCrossReg ψ c σ s u) :
    ∃ (N : ℕ) (γ : Fin N → ℝ → R3) (η m : ℝ), 0 < η ∧ 0 < m ∧
      (∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) ∧
      (∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t) ∧
      (∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
        ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
          Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
          (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s) ∧
      (∀ z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier, Submission.boxNorm c σ z = s →
        |z (σ 2) - (c (σ 2) + u)| < m → (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
          ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
             |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
        ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t) := by
  classical
  -- ## basic facts
  have hb2 : (0 : ℝ) < Submission.boxSide 2 := Submission.boxSide_pos 2
  have hb2s : (0 : ℝ) < Submission.boxSide 2 * s := mul_pos hb2 hs
  have hmarg : (0 : ℝ) < Submission.boxSide 2 * s - |u| := by linarith [hu]
  have hfund : IsCompact arcFundBox := isCompact_Icc.prod isCompact_Icc
  -- ## the per-pair cover of the face curves by the local arcs
  have hcover (i : Fin 3) (hi : i ≠ 2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
      ∃ θ : ℝ, 0 < θ ∧ ∀ p ∈ arcFundBox,
        (facePairMap ψ σ i p).1 = c (σ i) + ε * Submission.boxSide i * s →
        |(facePairMap ψ σ i p).2 - (c (σ 2) + u)| ≤ θ →
        p ∈ ⋃ p' ∈ crossSet ψ s u c σ i ε, (arcDatum ψ s u c σ i ε p').2.1 := by
    have hUo : IsOpen (⋃ p' ∈ crossSet ψ s u c σ i ε, (arcDatum ψ s u c σ i ε p').2.1) := by
      refine isOpen_biUnion fun p' hp' => ?_
      exact (arcDatum_spec ψ s u c σ i ε p' hi hε (mem_crossSet.mp hp').2
        (hX i hi ε hε p' (congrArg Prod.fst (mem_crossSet.mp hp').2)
          (congrArg Prod.snd (mem_crossSet.mp hp').2))).2.2.1
    refine exists_window_cover hfund ?_ ?_ hUo ?_
    · exact continuous_fst.comp (facePairMap_contDiff ψ σ i).continuous
    · exact continuous_snd.comp (facePairMap_contDiff ψ σ i).continuous
    · intro p hp h1 h2
      have hcross : facePairMap ψ σ i p =
          (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u) := by
        rw [Prod.ext_iff]; exact ⟨h1, h2⟩
      refine Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact mem_crossSet.mpr ⟨hp, hcross⟩
      · exact mem_of_mem_nhds (arcDatum_spec ψ s u c σ i ε p hi hε hcross
          (hX i hi ε hε p h1 h2)).2.1
  -- ## the thresholds
  let covθ : Fin 3 × ℝ → ℝ := fun q =>
    if h : q.1 ≠ 2 ∧ (q.2 = 1 ∨ q.2 = -1) then
      Classical.choose (hcover q.1 h.1 q.2 h.2) else 1
  have hcovθ_val : ∀ (q : Fin 3 × ℝ) (h : q.1 ≠ 2 ∧ (q.2 = 1 ∨ q.2 = -1)),
      covθ q = Classical.choose (hcover q.1 h.1 q.2 h.2) := by
    intro q h
    simp only [covθ]
    exact dif_pos h
  have hcovθ_pos : ∀ q ∈ branchPairs, 0 < covθ q := by
    intro q hq
    have h1 : q.1 ≠ 2 := (Finset.mem_filter.mp (Finset.mem_product.mp hq).1).2
    have h2 : q.2 = 1 ∨ q.2 = -1 := by
      have hh := (Finset.mem_product.mp hq).2
      simpa using hh
    rw [hcovθ_val q ⟨h1, h2⟩]
    exact (Classical.choose_spec (hcover q.1 h1 q.2 h2)).1
  have hcovθ_eq : ∀ (i : Fin 3) (hi : i ≠ 2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1),
      covθ (i, ε) = Classical.choose (hcover i hi ε hε) := by
    intro i hi ε hε
    exact hcovθ_val (i, ε) ⟨hi, hε⟩
  let ηcov : ℝ := if h : branchPairs.Nonempty then branchPairs.inf' h covθ else 1
  have hηcov_def : ηcov =
      (if h : branchPairs.Nonempty then branchPairs.inf' h covθ else 1) := rfl
  have hηcov_pos : 0 < ηcov := by
    by_cases h : branchPairs.Nonempty
    · rw [hηcov_def, dif_pos h]
      exact (Finset.lt_inf'_iff h).mpr fun q hq => hcovθ_pos q hq
    · rw [hηcov_def, dif_neg h]; norm_num
  have hηcov_le : ∀ (i : Fin 3) (hi : i ≠ 2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1),
      ηcov ≤ Classical.choose (hcover i hi ε hε) := by
    intro i hi ε hε
    have hmem := mem_branchPairs hi hε
    have hne : branchPairs.Nonempty := ⟨(i, ε), hmem⟩
    rw [hηcov_def, dif_pos hne, ← hcovθ_eq i hi ε hε]
    exact Finset.inf'_le covθ hmem
  -- ## the branch thresholds
  let B : Finset (FaceBranch ψ s u c σ) := branchFinset ψ s u c σ hX
  let θb : FaceBranch ψ s u c σ → ℝ := fun bb => (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2
  have hθb_pos : ∀ bb ∈ B, 0 < θb bb := by
    intro bb hbb
    exact (arcDatum_spec ψ s u c σ bb.i bb.ε bb.p bb.hi bb.hε bb.hcross
      (hX bb.i bb.hi bb.ε bb.hε bb.p (congrArg Prod.fst bb.hcross)
        (congrArg Prod.snd bb.hcross))).1
  let ηθ : ℝ := if h : B.Nonempty then B.inf' h θb else 1
  have hηθ_def : ηθ = (if h : B.Nonempty then B.inf' h θb else 1) := rfl
  have hηθ_pos : 0 < ηθ := by
    by_cases h : B.Nonempty
    · rw [hηθ_def, dif_pos h]
      exact (Finset.lt_inf'_iff h).mpr fun bb hbb => hθb_pos bb hbb
    · rw [hηθ_def, dif_neg h]; norm_num
  have hηθ_le : ∀ bb ∈ B, ηθ ≤ θb bb := by
    intro bb hbb
    have hne : B.Nonempty := ⟨bb, hbb⟩
    rw [hηθ_def, dif_pos hne]
    exact Finset.inf'_le θb hbb
  let η : ℝ := min ηcov ηθ
  let m : ℝ := min η ((Submission.boxSide 2 * s - |u|) / 2)
  have hηpos : 0 < η := lt_min hηcov_pos hηθ_pos
  have hmpos : 0 < m := lt_min hηpos (by linarith)
  have hmη : m ≤ η := min_le_left η _
  have hmmarg : m ≤ (Submission.boxSide 2 * s - |u|) / 2 := min_le_right η _
  -- ## the arcs
  let arc : FaceBranch ψ s u c σ → ℝ → R3 := fun bb t =>
    Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t)
  refine ⟨B.card, fun k => arc (B.equivFin.symm k).val, η, m, hηpos, hmpos, ?_, ?_, ?_, ?_⟩
  · -- the arcs are `C³`
    intro k
    set bb : FaceBranch ψ s u c σ := (B.equivFin.symm k).val with hbb
    have hbbB : bb ∈ B := (B.equivFin.symm k).property
    have hle : η ≤ (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 :=
      le_trans (min_le_right ηcov ηθ) (hηθ_le bb hbbB)
    have hmono : Set.Icc (-η) η ⊆
        Set.Icc (-(arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2)
          (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hspec := (arcDatum_spec ψ s u c σ bb.i bb.ε bb.p bb.hi bb.hε bb.hcross
      (hX bb.i bb.hi bb.ε bb.hε bb.p (congrArg Prod.fst bb.hcross)
        (congrArg Prod.snd bb.hcross))).2.2.2.1
    exact ContDiff.fun_comp_contDiffOn
      ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le (by decide)) (hspec.mono hmono)
  · -- the height identity
    intro k t ht
    set bb : FaceBranch ψ s u c σ := (B.equivFin.symm k).val with hbb
    have hbbB : bb ∈ B := (B.equivFin.symm k).property
    have hle : η ≤ (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 :=
      le_trans (min_le_right ηcov ηθ) (hηθ_le bb hbbB)
    have hmono : Set.Icc (-η) η ⊆
        Set.Icc (-(arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2)
          (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hspec := (arcDatum_spec ψ s u c σ bb.i bb.ε bb.p bb.hi bb.hε bb.hcross
      (hX bb.i bb.hi bb.ε bb.hε bb.p (congrArg Prod.fst bb.hcross)
        (congrArg Prod.snd bb.hcross))).2.2.2.2.2.1 t (hmono ht)
    exact congrArg Prod.snd hspec
  · -- the parametrisation data of each arc
    intro k
    set bb : FaceBranch ψ s u c σ := (B.equivFin.symm k).val with hbb
    have hbbB : bb ∈ B := (B.equivFin.symm k).property
    have hle : η ≤ (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 :=
      le_trans (min_le_right ηcov ηθ) (hηθ_le bb hbbB)
    have hmono : Set.Icc (-η) η ⊆
        Set.Icc (-(arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2)
          (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 :=
      fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hspec := arcDatum_spec ψ s u c σ bb.i bb.ε bb.p bb.hi bb.hε bb.hcross
      (hX bb.i bb.hi bb.ε bb.hε bb.p (congrArg Prod.fst bb.hcross)
        (congrArg Prod.snd bb.hcross))
    refine ⟨bb.i, bb.hi, bb.ε, bb.hε, (arcDatum ψ s u c σ bb.i bb.ε bb.p).1,
      hspec.2.2.2.1.mono hmono, ?_⟩
    intro t ht
    exact ⟨rfl, congrArg Prod.fst (hspec.2.2.2.2.2.1 t (hmono ht))⟩
  · -- the cover
    intro z hz hbn hband hnoedge
    obtain ⟨p, hpfund, hpz⟩ := exists_mem_arcFundBox_par_eq ψ hz
    obtain ⟨j, hj⟩ := exists_face_eq_of_boxNorm_eq hbn
    have hjne : j ≠ 2 := by
      intro hj2
      have h1 : |z (σ 2) - c (σ 2)| = Submission.boxSide 2 * s := by rw [← hj2]; exact hj
      have h2 : Submission.boxSide 2 * s - |u| ≤ |z (σ 2) - (c (σ 2) + u)| := by
        calc Submission.boxSide 2 * s - |u| = |z (σ 2) - c (σ 2)| - |u| := by rw [h1]
          _ ≤ |z (σ 2) - c (σ 2) - u| := abs_sub_abs_le_abs_sub _ _
          _ = |z (σ 2) - (c (σ 2) + u)| := by ring_nf
      have h3 : |z (σ 2) - (c (σ 2) + u)| < m := hband
      linarith [h2, h3, hmmarg, hmarg]
    obtain ⟨ε, hε, hzε⟩ : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
        z (σ j) = c (σ j) + ε * Submission.boxSide j * s := by
      by_cases h0 : 0 ≤ z (σ j) - c (σ j)
      · refine ⟨1, Or.inl rfl, ?_⟩
        rw [abs_of_nonneg h0] at hj
        linarith [hj]
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [abs_of_neg (lt_of_not_ge h0)] at hj
        linarith [hj]
    have hp1 : (facePairMap ψ σ j p).1 = c (σ j) + ε * Submission.boxSide j * s := by
      show (Work.BoxShrink.Pinch.par ψ p) (σ j) = _
      rw [hpz]; exact hzε
    have hp2 : |(facePairMap ψ σ j p).2 - (c (σ 2) + u)| ≤ η := by
      show |(Work.BoxShrink.Pinch.par ψ p) (σ 2) - (c (σ 2) + u)| ≤ η
      rw [hpz]
      exact le_trans (le_of_lt hband) hmη
    have hcoverj := Classical.choose_spec (hcover j hjne ε hε)
    have hθle : η ≤ Classical.choose (hcover j hjne ε hε) :=
      le_trans (min_le_left ηcov ηθ) (hηcov_le j hjne ε hε)
    have hpU := hcoverj.2 p hpfund hp1 (le_trans hp2 hθle)
    obtain ⟨p', hp'U⟩ := Set.mem_iUnion.mp hpU
    obtain ⟨hp'cs, hp'U⟩ := Set.mem_iUnion.mp hp'U
    set bb : FaceBranch ψ s u c σ :=
      ⟨j, ε, p', hjne, hε, (mem_crossSet.mp hp'cs).1, (mem_crossSet.mp hp'cs).2⟩ with hbb
    have hbbB : bb ∈ B := mem_branchFinset hjne hε hp'cs
    have hspecb := arcDatum_spec ψ s u c σ j ε p' hjne hε (mem_crossSet.mp hp'cs).2
      (hX j hjne ε hε p' (congrArg Prod.fst (mem_crossSet.mp hp'cs).2)
        (congrArg Prod.snd (mem_crossSet.mp hp'cs).2))
    have hp_eq : (arcDatum ψ s u c σ j ε p').1
        ((facePairMap ψ σ j p).2 - (c (σ 2) + u)) = p := hspecb.2.2.2.2.2.2 p hp'U hp1
    have hγbb : (fun k => arc (B.equivFin.symm k).val) (B.equivFin ⟨bb, hbbB⟩) = arc bb := by
      show arc (B.equivFin.symm (B.equivFin ⟨bb, hbbB⟩)).val = arc bb
      rw [Equiv.symm_apply_apply]
    have htmem : (facePairMap ψ σ j p).2 - (c (σ 2) + u) ∈ Set.Ioo (-η) η := by
      rw [Set.mem_Ioo, ← abs_lt]
      show |(Work.BoxShrink.Pinch.par ψ p) (σ 2) - (c (σ 2) + u)| < η
      rw [hpz]
      exact lt_of_lt_of_le hband hmη
    refine ⟨B.equivFin ⟨bb, hbbB⟩, (facePairMap ψ σ j p).2 - (c (σ 2) + u), htmem, ?_⟩
    rw [hγbb]
    show z = Work.BoxShrink.Pinch.par ψ
      ((arcDatum ψ s u c σ j ε p').1 ((facePairMap ψ σ j p).2 - (c (σ 2) + u)))
    rw [hp_eq]
    exact hpz.symm


end

end Work.Drive.Mono

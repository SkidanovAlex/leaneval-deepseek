import Mathlib
import Submission.Work.Drive.Mono.SphereFaceDefs
import Submission.Work.Drive.Mono.exists_ball_eq_of_fderiv_prod_invertible
import Submission.Work.Drive.Mono.carrier_unique_of_param_unique

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.Mono

noncomputable section

/-!
# The box-sphere/face-plane corner: closure and local uniqueness

At a point `z = par ψ p` of the surface which lies simultaneously on the box sphere
(`boxNorm c σ z = s`) and on the upper face of the tilted slab
(`⟂v,z⟂ = ⟂v,c⟂ + u + h`), with the two level functions non-degenerate and independent at `p`
(hypotheses `hd1`, `hd2`, `hd3`), this module proves the two analytic facts the local model of the
corner needs:

* `z` is in the **closure** of the open half-box `PBox s c σ ∩ {⟂v,·⟂ > ⟂v,c⟂ + u + h}`: the
  direction `r` supplied by Cramer's rule (`exists_apply_eq_pair_of_forall_ne_smul`) decreases the
  box norm and increases the slab coordinate at first order, so a small ray of the surface through
  `z` lies in the half-box and tends to `z`;
* the two level conditions have **no other common zero on the surface near `z`**: near `p`,
  `boxH = boxNorm ∘ par - s` is the maximum of the six pulled-back signed faces, and at every face
  which is active at `p` the pair `(faceW, planeG)` has an invertible derivative at `p` — hence is a
  local homeomorphism by the inverse function theorem — so its common zero set near `p` is `{p}`.

The helpers below are the ones the two arguments share: the two signs `faceSgn`, the extraction of
an active signed face from a zero of `boxH` (`exists_faceW_eq_zero_of_boxH_eq_zero`), and the
computation of the derivatives of `planeG` and `boxH` in the parameter plane.
-/

/-! ## The six signed faces -/

/-- The two signs `±1` indexing the two faces of a coordinate direction of the box. -/
def faceSgn : Fin 2 → ℝ := ![1, -1]

@[simp] theorem faceSgn_zero : faceSgn (0 : Fin 2) = 1 := rfl

@[simp] theorem faceSgn_one : faceSgn (1 : Fin 2) = -1 := rfl

theorem faceSgn_mem (j : Fin 2) : faceSgn j = 1 ∨ faceSgn j = -1 := by
  fin_cases j <;> simp

/-- If `max a b = 0` then one of `a`, `b` vanishes. -/
private lemma or_of_max_eq_zero {a b : ℝ} (h : max a b = 0) : a = 0 ∨ b = 0 := by
  rcases le_total a b with hab | hab
  · exact Or.inr (by rw [max_eq_right hab] at h; exact h)
  · exact Or.inl (by rw [max_eq_left hab] at h; exact h)

/-- The maximum of the six pulled-back signed faces, arranged in the binary tree in which
`boxH_eq_max_three` exhibits `boxH`, vanishes only if one of the six does. -/
private lemma or_of_max_six_eq_zero {a b c d e f : ℝ}
    (h : max (max (max a b) (max c d)) (max e f) = 0) :
    a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 ∨ e = 0 ∨ f = 0 := by
  rcases or_of_max_eq_zero h with h1 | h1
  · rcases or_of_max_eq_zero h1 with h2 | h2
    · rcases or_of_max_eq_zero h2 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inl h3)
    · rcases or_of_max_eq_zero h2 with h3 | h3
      · exact Or.inr (Or.inr (Or.inl h3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h3)))
  · rcases or_of_max_eq_zero h1 with h3 | h3
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h3))))

/-- **An active signed face over a zero of `boxH`.**  If the pulled-back box norm is `s` at `q`
(i.e. `boxH q = 0`), then one of the six signed faces `faceW i ε` (`ε = ±1`) vanishes at `q`. -/
theorem exists_faceW_eq_zero_of_boxH_eq_zero {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {q : ℝ × ℝ} (h : boxH ψ s c σ q = 0) :
    ∃ x : Fin 3 × Fin 2, faceW ψ s c σ x.1 (faceSgn x.2) q = 0 := by
  have h6 : max (max (max (faceW ψ s c σ 0 1 q)
        (faceW ψ s c σ 0 (-1) q))
      (max (faceW ψ s c σ 1 1 q) (faceW ψ s c σ 1 (-1) q)))
      (max (faceW ψ s c σ 2 1 q) (faceW ψ s c σ 2 (-1) q)) = 0 := by
    rw [← h, boxH_eq_max_three, faceMaxW_apply, faceMaxW_apply, faceMaxW_apply]
  rcases or_of_max_six_eq_zero h6 with h1 | h1 | h1 | h1 | h1 | h1
  · exact ⟨(0, 0), by simpa using h1⟩
  · exact ⟨(0, 1), by simpa using h1⟩
  · exact ⟨(1, 0), by simpa using h1⟩
  · exact ⟨(1, 1), by simpa using h1⟩
  · exact ⟨(2, 0), by simpa using h1⟩
  · exact ⟨(2, 1), by simpa using h1⟩

/-! ## Derivatives in the parameter plane -/

/-- The pulled-back slab coordinate is `C^∞`. -/
theorem contDiff_planeG (ψ : Submission.Diffeo) (c v : R3) (u h : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (planeG ψ c v u h) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) :=
    (innerSL ℝ v).contDiff.comp (Work.BoxShrink.Pinch.par_contDiff ψ)
  exact h1.sub contDiff_const

/-- The derivative of the pulled-back slab coordinate is that of the pulled-back inner product. -/
theorem fderiv_planeG (ψ : Submission.Diffeo) (c v : R3) (u h : ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (planeG ψ c v u h) p =
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p := by
  change fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)
    - (inner ℝ v c + u + h)) p = _
  rw [fderiv_sub_const]

/-- The derivative of the shifted pulled-back box norm is that of the pulled-back box norm. -/
theorem fderiv_boxH (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (p : ℝ × ℝ) :
    fderiv ℝ (boxH ψ s c σ) p =
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
  change fderiv ℝ (fun q : ℝ × ℝ =>
    Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) - s) p = _
  rw [fderiv_sub_const]

/-! ## The point `z` is a limit of points of the half-box -/

/-- **`z` lies in the closure of the open half-box.**

The independence of the two derivatives at `p` supplies a direction `r` with
`d(boxNorm ∘ par)(r) = -1` and `d(inner v ∘ par)(r) = 1`; the surface curve `t ↦ par ψ (p + t • r)`
is then, for small `t > 0`, inside `PBox s c σ` and strictly above the slab face, and it tends to
`z` as `t → 0⁺`. -/
theorem closure_of_sphereFace {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {z : R3} {p : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzface : inner ℝ v z = inner ℝ v c + u + h)
    (hd1 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd2 : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd3 : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    z ∈ closure (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y}) := by
  set L : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p with hLdef
  set M : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p with hMdef
  obtain ⟨r, hr1, hr2⟩ :=
    exists_apply_eq_pair_of_forall_ne_smul hd2 hd3 (1 : ℝ) (-1 : ℝ)
  have hBdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
    by_contra hc
    exact hd2 (fderiv_zero_of_not_differentiableAt hc)
  -- moving along `r` decreases the box norm
  have hBlt : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ (p + t • r)) < s := by
    have hF : HasFDerivAt
        (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) M p :=
      hBdiff.hasFDerivAt
    have hMr : M r < 0 := by rw [hr2]; norm_num
    filter_upwards [eventually_lt_self_of_fderiv_smul_neg hF hMr] with t ht
    simpa [hp, hzsphere] using ht
  have hGdiff : DifferentiableAt ℝ (planeG ψ c v u h) p :=
    ((contDiff_planeG ψ c v u h).differentiable (by simp)).differentiableAt
  -- and increases the slab coordinate
  have hGgt : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      inner ℝ v c + u + h < inner ℝ v (Work.BoxShrink.Pinch.par ψ (p + t • r)) := by
    have hneg0 : HasFDerivAt (fun q : ℝ × ℝ => - (planeG ψ c v u h) q)
        (-(fderiv ℝ (planeG ψ c v u h) p)) p := hGdiff.hasFDerivAt.neg
    have hneg : HasFDerivAt (fun q : ℝ × ℝ => - (planeG ψ c v u h) q) (-L) p := by
      rw [hLdef, ← fderiv_planeG ψ c v u h p]
      exact hneg0
    have hkey : (-L) r < 0 := by
      rw [show (-L) r = -(L r) by simp, hr1]; norm_num
    have hkey' : (fderiv ℝ (fun q : ℝ × ℝ => - (planeG ψ c v u h) q) p) r < 0 := by
      rw [hneg.fderiv]; exact hkey
    have hneg' : HasFDerivAt (fun q : ℝ × ℝ => - (planeG ψ c v u h) q)
        (fderiv ℝ (fun q : ℝ × ℝ => - (planeG ψ c v u h) q) p) p := by
      rw [hneg.fderiv]; exact hneg
    filter_upwards [eventually_lt_self_of_fderiv_smul_neg hneg' hkey'] with t ht
    simp only [neg_lt_neg_iff] at ht
    have hGp : planeG ψ c v u h p = 0 := by
      rw [planeG_apply, hp, hzface]; ring
    rw [hGp] at ht
    rw [planeG_apply] at ht
    linarith
  have hcomb : ∀ᶠ t in 𝓝[>] (0 : ℝ), Work.BoxShrink.Pinch.par ψ (p + t • r) ∈
      Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y} := by
    filter_upwards [hBlt, hGgt] with t ht1 ht2
    exact ⟨(Submission.mem_PBox_iff s c σ _).mpr ht1, ht2⟩
  -- the curve tends to `z`
  have htend : Tendsto (fun t : ℝ => Work.BoxShrink.Pinch.par ψ (p + t • r))
      (𝓝[>] (0 : ℝ)) (𝓝 z) := by
    have hcont : Continuous (fun t : ℝ => Work.BoxShrink.Pinch.par ψ (p + t • r)) := by
      refine (Work.BoxShrink.Pinch.par_continuous ψ).comp ?_
      exact continuous_const.add (continuous_id.smul continuous_const)
    have hh0 : Tendsto (fun t : ℝ => Work.BoxShrink.Pinch.par ψ (p + t • r))
        (𝓝 (0 : ℝ)) (𝓝 z) := by
      have h := hcont.tendsto (0 : ℝ)
      have h2 : Work.BoxShrink.Pinch.par ψ (p + (0 : ℝ) • r) = z := by simp [hp]
      rw [h2] at h
      exact h
    exact hh0.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  exact mem_closure_iff_frequently.mpr (htend.frequently (hcomb.frequently))

/-! ## Uniqueness of the common zero in the parameter plane -/

/-- **The two level conditions have no other common zero near `p`.**

`boxH = boxNorm ∘ par - s` is the maximum of the six pulled-back signed faces.  At a face which is
active at `p` (`faceW i ε p = 0`), the difference `boxH - faceW i ε ≥ 0` has a local minimum at
`p`, so the derivative of `faceW i ε` at `p` equals that of `boxH`; the pair `(faceW i ε, planeG)`
therefore has an invertible derivative at `p` and hence is a local homeomorphism near `p`
(`exists_ball_eq_of_fderiv_prod_invertible`), whose common zero set is `{p}` there.  The faces
which are not active at `p` are strictly negative nearby, by continuity. -/
theorem param_unique_of_sphereFace {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {z : R3} {p : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzface : inner ℝ v z = inner ℝ v c + u + h)
    (hd1 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd2 : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd3 : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × ℝ, dist q p < δ →
      boxH ψ s c σ q = 0 → planeG ψ c v u h q = 0 → q = p := by
  set L : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p with hLdef
  set M : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p with hMdef
  have hBdiff : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
    by_contra hc
    exact hd2 (fderiv_zero_of_not_differentiableAt hc)
  have hboxHdiff : DifferentiableAt ℝ (boxH ψ s c σ) p := hBdiff.sub_const s
  have hboxHfderiv : fderiv ℝ (boxH ψ s c σ) p = M := by
    rw [hMdef]; exact fderiv_boxH ψ s c σ p
  have hboxHp : boxH ψ s c σ p = 0 := by
    rw [boxH_apply, hp, hzsphere]; ring
  have hplaneGp : planeG ψ c v u h p = 0 := by
    rw [planeG_apply, hp, hzface]; ring
  have hplaneGfderiv : fderiv ℝ (planeG ψ c v u h) p = L := by
    rw [hLdef]; exact fderiv_planeG ψ c v u h p
  have hfaceWdiff : ∀ (i : Fin 3) (ε : ℝ), DifferentiableAt ℝ (faceW ψ s c σ i ε) p :=
    fun i ε => ((contDiff_faceW ψ s c σ i ε).differentiable (by simp)).differentiableAt
  -- an active face has the same derivative as `boxH`
  have hact_fderiv : ∀ (i : Fin 3) (ε : ℝ), (ε = 1 ∨ ε = -1) → faceW ψ s c σ i ε p = 0 →
      fderiv ℝ (faceW ψ s c σ i ε) p = M := by
    intro i ε hε hact
    have hmin : IsLocalMin (fun q : ℝ × ℝ => boxH ψ s c σ q - faceW ψ s c σ i ε q) p :=
      Filter.Eventually.of_forall (fun q => by
        have h1 := faceW_le_boxH ψ s c σ i ε hε q
        have h0 : boxH ψ s c σ p - faceW ψ s c σ i ε p = 0 := by rw [hboxHp, hact, sub_zero]
        show boxH ψ s c σ p - faceW ψ s c σ i ε p ≤ boxH ψ s c σ q - faceW ψ s c σ i ε q
        rw [h0]; linarith)
    have hfsub : fderiv ℝ (fun q : ℝ × ℝ => boxH ψ s c σ q - faceW ψ s c σ i ε q) p
        = fderiv ℝ (boxH ψ s c σ) p - fderiv ℝ (faceW ψ s c σ i ε) p := by
      rw [show (fun q : ℝ × ℝ => boxH ψ s c σ q - faceW ψ s c σ i ε q)
          = boxH ψ s c σ - faceW ψ s c σ i ε from rfl]
      exact fderiv_sub hboxHdiff (hfaceWdiff i ε)
    have hzero := hmin.fderiv_eq_zero
    rw [hfsub, hboxHfderiv] at hzero
    exact (sub_eq_zero.mp hzero).symm
  -- per-face data at each of the six faces
  have hpair : ∀ x : Fin 3 × Fin 2, ∃ δ : ℝ, 0 < δ ∧
      (∀ q : ℝ × ℝ, dist q p < δ → faceW ψ s c σ x.1 (faceSgn x.2) q = 0 →
        planeG ψ c v u h q = 0 → q = p) ∧
      (faceW ψ s c σ x.1 (faceSgn x.2) p < 0 →
        ∀ q : ℝ × ℝ, dist q p < δ → faceW ψ s c σ x.1 (faceSgn x.2) q < 0) := by
    rintro ⟨i, j⟩
    have hε : faceSgn j = 1 ∨ faceSgn j = -1 := faceSgn_mem j
    by_cases hact : faceW ψ s c σ i (faceSgn j) p = 0
    · -- the face is active: the pair `(faceW, planeG)` is a local homeomorphism at `p`
      have hfne : fderiv ℝ (faceW ψ s c σ i (faceSgn j)) p ≠ 0 := by
        rw [hact_fderiv i (faceSgn j) hε hact]; exact hd2
      have hind : ∀ t : ℝ, fderiv ℝ (planeG ψ c v u h) p ≠
          t • fderiv ℝ (faceW ψ s c σ i (faceSgn j)) p := by
        intro t ht
        refine hd3 t ?_
        rw [← hplaneGfderiv, ht, hact_fderiv i (faceSgn j) hε hact]
      obtain ⟨δ, hδpos, hδ⟩ := exists_ball_eq_of_fderiv_prod_invertible
        ((contDiff_faceW ψ s c σ i (faceSgn j)).of_le (by simp))
        ((contDiff_planeG ψ c v u h).of_le (by simp)) hfne hind
      refine ⟨δ, hδpos, ?_, ?_⟩
      · intro q hq hfw hpl
        exact hδ q hq (hfw.trans hact.symm) (hpl.trans hplaneGp.symm)
      · intro hlt
        exact absurd hlt (by rw [hact]; exact lt_irrefl 0)
    · -- the face is not active: it stays strictly negative near `p`
      have hlt : faceW ψ s c σ i (faceSgn j) p < 0 := by
        have hle := faceW_le_boxH ψ s c σ i (faceSgn j) hε p
        rw [hboxHp] at hle
        exact lt_of_le_of_ne hle hact
      obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
        ((isOpen_lt (contDiff_faceW ψ s c σ i (faceSgn j)).continuous continuous_const).mem_nhds hlt)
      refine ⟨δ, hδpos, ?_, ?_⟩
      · intro q hq hfw _
        exact absurd hfw (ne_of_lt (hδ hq))
      · intro _ q hq
        exact hδ hq
  set δx : Fin 3 × Fin 2 → ℝ := fun x => Classical.choose (hpair x) with hδxdef
  have hδxspec : ∀ x : Fin 3 × Fin 2, 0 < δx x ∧
      (∀ q : ℝ × ℝ, dist q p < δx x → faceW ψ s c σ x.1 (faceSgn x.2) q = 0 →
        planeG ψ c v u h q = 0 → q = p) ∧
      (faceW ψ s c σ x.1 (faceSgn x.2) p < 0 →
        ∀ q : ℝ × ℝ, dist q p < δx x → faceW ψ s c σ x.1 (faceSgn x.2) q < 0) :=
    fun x => Classical.choose_spec (hpair x)
  refine ⟨Finset.inf' Finset.univ Finset.univ_nonempty δx, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr (fun x _ => (hδxspec x).1)
  · intro q hq hbox hplane
    have hdistx : ∀ x, dist q p < δx x := fun x =>
      lt_of_lt_of_le hq (Finset.inf'_le δx (Finset.mem_univ x))
    obtain ⟨x, hx⟩ := exists_faceW_eq_zero_of_boxH_eq_zero (ψ := ψ) (s := s) (c := c)
      (σ := σ) hbox
    rcases (hδxspec x).2 with ⟨hgood, hbad⟩
    by_cases hact : faceW ψ s c σ x.1 (faceSgn x.2) p = 0
    · exact hgood q (hdistx x) hx hplane
    · have hlt : faceW ψ s c σ x.1 (faceSgn x.2) p < 0 := by
        have hle := faceW_le_boxH ψ s c σ x.1 (faceSgn x.2) (faceSgn_mem x.2) p
        rw [hboxHp] at hle
        exact lt_of_le_of_ne hle hact
      exact absurd hx (ne_of_lt (hbad hlt q (hdistx x)))

/-! ## The corner: closure and uniqueness -/

/-- Route hints.  (1) `hd2` gives (via `fderiv_zero_of_not_differentiableAt`) that
`q ↦ boxNorm c σ (par ψ q)` is differentiable at `p`, and `hd1`/`hd3` say that the two functionals
`fderiv (inner v ∘ par) p` and `fderiv (boxNorm ∘ par) p` are non-zero and independent; so Cramer
(`exists_apply_eq_pair_of_forall_ne_smul` in `SphereFaceDefs`) supplies `r` with
`(fderiv (inner v ∘ par) p) r = 1` and `(fderiv (boxNorm ∘ par) p) r = -1`.  Then
`eventually_lt_self_of_fderiv_smul_neg` (also in `SphereFaceDefs`) shows that for small `t > 0` the
point `par ψ (p + t • r)` is in `PBox` and strictly above the face plane, and it tends to `z`, which
is the first conjunct.

(2) For the uniqueness, `boxH := boxNorm ∘ par - s` is the maximum of the six pulled-back signed
faces `faceW i ε` (`boxH_eq_max_three`, `faceW_le_boxH`). If `faceW i ε p = 0` then
`faceW i ε p ≤ boxH p = 0` with equality, so `IsLocalMin.fderiv_eq_zero` applied to
`boxH - faceW i ε` gives `fderiv (faceW i ε) p = fderiv boxH p`.  Hence for such an active `(i, ε)`
the pair `(faceW i ε, planeG)` has invertible derivative at `p`
(`isInvertible_prod_of_forall_ne_smul`), so it is a local homeomorphism
(`HasStrictFDerivAt.toOpenPartialHomeomorph`, as in `isLocallyArc_max_of_invertible`) and its
common zero set is `{p}` near `p`.  Since every zero of `boxH` near `p` is a zero of one of the
six `faceW`s and the non-active ones are `≠ 0` near `p` (they are `< 0` there by continuity), some
`δ > 0` satisfies: `q ∈ ball p δ → boxH q = 0 → planeG q = 0 → q = p`.  Finally `par ψ '' ball p δ`
is open in the carrier (`isOpenInCarrier_image_of_isOpen`), so there is `ρ₀ > 0` with
`ball z ρ₀ ∩ carrier ⊆ par ψ '' ball p δ`; a surface point of that ball with both level conditions
then has a parameter point in `ball p δ`, hence is `z`. -/
theorem closure_and_uniqueness_of_sphereFace {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {z : R3} {p : ℝ × ℝ}
    (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hzsphere : Submission.boxNorm c σ z = s)
    (hzface : inner ℝ v z = inner ℝ v c + u + h)
    (hd1 : fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd2 : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hd3 : ∀ t : ℝ, fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p) :
    (z ∈ closure (Submission.PBox s c σ ∩ {y : R3 | inner ℝ v c + u + h < inner ℝ v y})) ∧
    (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ y : R3, y ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        dist y z < ρ₀ → Submission.boxNorm c σ y = s →
        inner ℝ v y = inner ℝ v c + u + h → y = z) := by
  refine ⟨closure_of_sphereFace hp hzsphere hzface hd1 hd2 hd3, ?_⟩
  exact carrier_unique_of_param_unique hp
    (param_unique_of_sphereFace hp hzsphere hzface hd1 hd2 hd3)

end

end Work.Drive.Mono

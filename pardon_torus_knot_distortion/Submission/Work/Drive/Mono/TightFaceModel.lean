import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceData

/-!
# The local model of the box norm at a wall ∩ box-sphere junction

At a point `z` of the box sphere `{boxNorm c σ · = s}` (with `s > 0`) at which the surface crosses
the level wall `{ℓ = lam}` transversally, the trace of the tilted sweep near `z` is the union of the
half of the box-sphere trace on the side `ℓ ≥ lam` and of the half of the wall trace inside the box.
In the parameter plane this local model is the zero set of

`q ↦ max (max over the tight faces i of z (faceLin c σ i εᵢ (par q) - s)) (lam - ℓ (par q))`,

where `εᵢ` is the sign of the `σ i`-th coordinate of `z - c` and the tight faces are those with
`faceNorm c σ i z = s`.

This module supplies the analytic facts about the box norm that the identification uses:

* `eventually_boxNorm_eq_sup_tight` — near `z`, the box norm is the maximum of the tight signed
  faces (the other faces are uniformly below);
* `fderiv_tightFace_sub_s_eq` — the pull-back of every tight signed face has at `p` the same
  derivative as the pull-back of the box norm: their difference is `≥ 0` everywhere with a zero at
  `p`, so `p` is a global minimum of it.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

namespace Work.Drive.Mono

noncomputable section

/-- The sign of the `σ i`-th coordinate of `z - c`, as a number in `{1, -1}` (junk value `1` when
the coordinate vanishes). -/
def tightEps (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (i : Fin 3) : ℝ :=
  if 0 ≤ z (σ i) - c (σ i) then 1 else -1

theorem tightEps_eq_one_or_neg_one (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (i : Fin 3) :
    tightEps c σ z i = 1 ∨ tightEps c σ z i = -1 := by
  rw [tightEps]
  split_ifs with h
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `tightEps` is the sign of the coordinate: it multiplies the coordinate back to its absolute
value. -/
theorem tightEps_mul_signedFace (c : R3) (σ : Equiv.Perm (Fin 3)) (z : R3) (i : Fin 3) :
    Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) z =
      Work.Smooth.BoxGeneric.faceNorm c σ i z := by
  have hkey : tightEps c σ z i * (z (σ i) - c (σ i)) = |z (σ i) - c (σ i)| := by
    rw [tightEps]
    split_ifs with h
    · rw [abs_of_nonneg h]; ring
    · push Not at h
      rw [abs_of_neg h]; ring
  rw [Work.Smooth.BoxGeneric.faceLin_apply, Work.Smooth.BoxGeneric.signedFace,
    Work.Smooth.BoxGeneric.faceNorm_apply, ← hkey, mul_div_assoc]

/-- The tight faces of the box sphere of level `s` at `z`. -/
abbrev TightFaceIdx (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (z : R3) : Type :=
  {i : Fin 3 // Work.Smooth.BoxGeneric.faceNorm c σ i z = s}

theorem tightFaceIdx_nonempty {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    (hz : Submission.boxNorm c σ z = s) : Nonempty (TightFaceIdx c σ s z) := by
  obtain ⟨i, hi⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ z
  exact ⟨⟨i, by rw [hi, hz]⟩⟩

/-- The canonical nonemptiness of the set of tight faces. -/
theorem tightIdx_nonempty {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    (hz : Submission.boxNorm c σ z = s) :
    (Finset.univ : Finset (TightFaceIdx c σ s z)).Nonempty := by
  obtain ⟨i, hi⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ z
  exact ⟨⟨i, by rw [hi, hz]⟩, Finset.mem_univ _⟩

/-- The supremum over a nonempty finset does not depend on the proof of nonemptiness. -/
theorem finset_sup'_proof_irrel {β : Type*} {α : Type*} [SemilatticeSup α] {t : Finset β}
    (H H' : t.Nonempty) (f : β → α) : t.sup' H f = t.sup' H' f := by
  refine le_antisymm (Finset.sup'_le H f (fun i hi => Finset.le_sup' (s := t) f hi))
    (Finset.sup'_le H' f (fun i hi => Finset.le_sup' (s := t) f hi))

/-- The maximum of the tight signed faces at the point `y`. -/
noncomputable def tightSup (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (z : R3)
    (hz : Submission.boxNorm c σ z = s) (y : R3) : ℝ :=
  (Finset.univ : Finset (TightFaceIdx c σ s z)).sup' (tightIdx_nonempty hz)
    (fun i => Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1) y)

/-- A tight signed face is dominated by the maximum of the tight signed faces. -/
theorem le_tightSup {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    (hz : Submission.boxNorm c σ z = s) (i : Fin 3)
    (hi : Work.Smooth.BoxGeneric.faceNorm c σ i z = s) (y : R3) :
    Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) y ≤ tightSup c σ s z hz y := by
  haveI : Nonempty (TightFaceIdx c σ s z) := ⟨(⟨i, hi⟩ : TightFaceIdx c σ s z)⟩
  have h1 : Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) y
      ≤ (Finset.univ : Finset (TightFaceIdx c σ s z)).sup' Finset.univ_nonempty
          (fun j : TightFaceIdx c σ s z =>
            Work.Smooth.BoxGeneric.faceLin c σ j.1 (tightEps c σ z j.1) y) :=
    Finset.le_sup' (s := (Finset.univ : Finset (TightFaceIdx c σ s z)))
      (fun j : TightFaceIdx c σ s z =>
        Work.Smooth.BoxGeneric.faceLin c σ j.1 (tightEps c σ z j.1) y)
      (Finset.mem_univ (⟨i, hi⟩ : TightFaceIdx c σ s z))
  rw [finset_sup'_proof_irrel Finset.univ_nonempty (tightIdx_nonempty hz) _] at h1
  rw [tightSup]
  exact h1

/-- The maximum of the tight signed faces is dominated by any common bound. -/
theorem tightSup_le {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    (hz : Submission.boxNorm c σ z = s) {y : R3} {a : ℝ}
    (h : ∀ i : TightFaceIdx c σ s z,
      Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1) y ≤ a) :
    tightSup c σ s z hz y ≤ a := by
  rw [tightSup]
  exact Finset.sup'_le _ _ (fun i _ => h i)

/-- The signed face function of a tight face is `s` at `z`. -/
theorem faceLin_tightEps_tight_eq {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3} {i : Fin 3}
    (hi : Work.Smooth.BoxGeneric.faceNorm c σ i z = s) :
    Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) z = s := by
  rw [tightEps_mul_signedFace, hi]

/-- Near a tight face, the face norm is the signed face function: the sign of the corresponding
coordinate is locally constant. -/
theorem eventually_faceNorm_eq_faceLin_tight {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    {i : Fin 3} (hs : 0 < s) (hi : Work.Smooth.BoxGeneric.faceNorm c σ i z = s) :
    ∀ᶠ y in 𝓝 z, Work.Smooth.BoxGeneric.faceNorm c σ i y =
      Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) y := by
  have hne : z (σ i) - c (σ i) ≠ 0 := by
    intro h0
    have h1 : Work.Smooth.BoxGeneric.faceNorm c σ i z = 0 := by
      rw [Work.Smooth.BoxGeneric.faceNorm_apply, h0, abs_zero, zero_div]
    rw [h1] at hi
    exact (ne_of_gt hs) hi.symm
  have hcont : Continuous (fun y : R3 => y (σ i) - c (σ i)) := by fun_prop
  rw [tightEps]
  split_ifs with h
  · filter_upwards [hcont.isOpen_preimage _ isOpen_Ioi |>.mem_nhds
        (show (0:ℝ) < z (σ i) - c (σ i) from lt_of_le_of_ne h (Ne.symm hne))] with y hy
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, Work.Smooth.BoxGeneric.faceLin_one,
      Work.Smooth.BoxGeneric.signedFace, abs_of_pos hy]
  · push Not at h
    filter_upwards [hcont.isOpen_preimage _ isOpen_Iio |>.mem_nhds h] with y hy
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, Work.Smooth.BoxGeneric.faceLin_neg_one,
      Work.Smooth.BoxGeneric.signedFace, abs_of_neg hy]
    ring

/-- **The box norm is, near a point of the box sphere, the maximum of the tight signed faces.**
The faces which are not tight at `z` are uniformly dominated by the tight ones, and the box norm is
the maximum of the six signed faces. -/
theorem eventually_boxNorm_eq_sup_tight {c : R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {z : R3}
    (hs : 0 < s) (hz : Submission.boxNorm c σ z = s) :
    ∀ᶠ y in 𝓝 z, Submission.boxNorm c σ y = tightSup c σ s z hz y := by
  classical
  have hsign : ∀ᶠ y in 𝓝 z, ∀ i : Fin 3, Work.Smooth.BoxGeneric.faceNorm c σ i z = s →
      Work.Smooth.BoxGeneric.faceNorm c σ i y =
        Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) y := by
    rw [Filter.eventually_all]
    intro i
    by_cases hi : Work.Smooth.BoxGeneric.faceNorm c σ i z = s
    · filter_upwards [eventually_faceNorm_eq_faceLin_tight hs hi] with y hy
      intro _
      exact hy
    · filter_upwards with y
      intro h
      exact absurd h hi
  have hdom : ∀ᶠ y in 𝓝 z, ∀ p : Fin 3 × Fin 3,
      Work.Smooth.BoxGeneric.faceNorm c σ p.1 z < s →
      Work.Smooth.BoxGeneric.faceNorm c σ p.2 z = s →
      Work.Smooth.BoxGeneric.faceNorm c σ p.1 y < Work.Smooth.BoxGeneric.faceNorm c σ p.2 y := by
    rw [Filter.eventually_all]
    intro p
    by_cases hp : Work.Smooth.BoxGeneric.faceNorm c σ p.1 z < s ∧
        Work.Smooth.BoxGeneric.faceNorm c σ p.2 z = s
    · have hcont : Continuous (fun y : R3 =>
          Work.Smooth.BoxGeneric.faceNorm c σ p.1 y - Work.Smooth.BoxGeneric.faceNorm c σ p.2 y) := by
        have h1 : Continuous (fun y : R3 => Work.Smooth.BoxGeneric.faceNorm c σ p.1 y) := by
          simp only [Work.Smooth.BoxGeneric.faceNorm_apply]; fun_prop
        have h2 : Continuous (fun y : R3 => Work.Smooth.BoxGeneric.faceNorm c σ p.2 y) := by
          simp only [Work.Smooth.BoxGeneric.faceNorm_apply]; fun_prop
        exact h1.sub h2
      have hneg : (fun y : R3 => Work.Smooth.BoxGeneric.faceNorm c σ p.1 y -
          Work.Smooth.BoxGeneric.faceNorm c σ p.2 y) z < 0 := by
        show Work.Smooth.BoxGeneric.faceNorm c σ p.1 z -
          Work.Smooth.BoxGeneric.faceNorm c σ p.2 z < 0
        rw [hp.2]
        linarith [hp.1]
      filter_upwards [hcont.isOpen_preimage _ isOpen_Iio |>.mem_nhds hneg] with y hy
      intro _ _
      exact sub_neg.mp hy
    · filter_upwards with y
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hp
  filter_upwards [hsign, hdom] with y hysig hydom
  refine le_antisymm ?_ ?_
  · obtain ⟨i₀, hi₀⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ y
    rw [← hi₀]
    by_cases ht : Work.Smooth.BoxGeneric.faceNorm c σ i₀ z = s
    · rw [hysig i₀ ht]
      exact le_tightSup hz i₀ ht y
    · obtain ⟨j₀, hj₀⟩ := Work.Smooth.BoxGeneric.exists_faceNorm_eq_boxNorm c σ z
      have hjs : Work.Smooth.BoxGeneric.faceNorm c σ j₀ z = s := by rw [hj₀, hz]
      have hlt : Work.Smooth.BoxGeneric.faceNorm c σ i₀ z < s := by
        refine lt_of_le_of_ne ?_ ht
        rw [← hz]
        exact Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i₀ z
      exact le_of_lt (calc Work.Smooth.BoxGeneric.faceNorm c σ i₀ y
          < Work.Smooth.BoxGeneric.faceNorm c σ j₀ y := hydom (i₀, j₀) hlt hjs
        _ = Work.Smooth.BoxGeneric.faceLin c σ j₀ (tightEps c σ z j₀) y := hysig j₀ hjs
        _ ≤ tightSup c σ s z hz y := le_tightSup hz j₀ hjs y)
  · refine tightSup_le hz (fun i => ?_)
    show Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1) y ≤ Submission.boxNorm c σ y
    calc Work.Smooth.BoxGeneric.faceLin c σ i.1 (tightEps c σ z i.1) y
        ≤ Work.Smooth.BoxGeneric.faceNorm c σ i.1 y := by
          rw [Work.Smooth.BoxGeneric.faceNorm_eq_max_faceLin]
          rcases tightEps_eq_one_or_neg_one c σ z i.1 with h | h <;> rw [h]
          · exact le_max_left _ _
          · rw [Work.Smooth.BoxGeneric.faceLin_neg_one]; exact le_max_right _ _
      _ ≤ Submission.boxNorm c σ y := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i.1 y

/-- For a nonempty finite family of reals, subtracting a constant subtracts it from the supremum. -/
theorem finset_sup_sub_eq {β : Type*} {t : Finset β} (H : t.Nonempty) (f : β → ℝ) (c : ℝ) :
    t.sup' H (fun i => f i - c) = t.sup' H f - c := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le H (fun i => f i - c) (fun i hi => ?_)
    have h1 : f i ≤ t.sup' H f := Finset.le_sup' (s := t) f hi
    linarith
  · obtain ⟨i, hi, hmax⟩ := Finset.exists_mem_eq_sup' H f
    calc t.sup' H f - c = f i - c := by rw [hmax]
      _ ≤ t.sup' H (fun j => f j - c) := Finset.le_sup' (s := t) (fun j => f j - c) hi

/-- **The derivative of a tight signed face, pulled back to the parameter plane, is the derivative
of the pulled-back box norm.**  The difference of the two functions is nonnegative everywhere and
vanishes at `p`, so `p` is a global minimum of it. -/
theorem fderiv_tightFace_sub_s_eq {ψ : Submission.Diffeo} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {s : ℝ} {z : R3} {i : Fin 3} (hs : 0 < s) (hz : Submission.boxNorm c σ z = s)
    (hi : Work.Smooth.BoxGeneric.faceNorm c σ i z = s)
    {p : ℝ × ℝ} (hp : Work.BoxShrink.Pinch.par ψ p = z)
    (hD : fderiv ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0) :
    fderiv ℝ (fun q : ℝ × ℝ =>
        Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) (Work.BoxShrink.Pinch.par ψ q) - s) p
      = fderiv ℝ (fun q : ℝ × ℝ =>
        Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p := by
  classical
  set B : ℝ × ℝ → ℝ := fun q => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q) with hBdef
  set L : ℝ × ℝ → ℝ := fun q =>
    Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) (Work.BoxShrink.Pinch.par ψ q) with hLdef
  have hLcd : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) L :=
    Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i (tightEps c σ z i)
  have hLdiff : DifferentiableAt ℝ L p :=
    (hLcd.differentiable (by simp)).differentiableAt
  have hBdiff : DifferentiableAt ℝ B p := by
    by_contra h
    exact hD (fderiv_zero_of_not_differentiableAt h)
  have hnonneg : ∀ q : ℝ × ℝ, 0 ≤ B q - L q := by
    intro q
    have h1 : Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) (Work.BoxShrink.Pinch.par ψ q)
        ≤ Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ q) := by
      rw [Work.Smooth.BoxGeneric.faceNorm_eq_max_faceLin]
      rcases tightEps_eq_one_or_neg_one c σ z i with h | h <;> rw [h]
      · exact le_max_left _ _
      · rw [Work.Smooth.BoxGeneric.faceLin_neg_one]; exact le_max_right _ _
    have h2 := Work.Smooth.BoxGeneric.faceNorm_le_boxNorm c σ i (Work.BoxShrink.Pinch.par ψ q)
    linarith
  have hzero : B p - L p = 0 := by
    have h1 : L p = Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) z := by
      rw [hLdef]; exact congrArg _ hp
    have h2 : Work.Smooth.BoxGeneric.faceLin c σ i (tightEps c σ z i) z = s :=
      faceLin_tightEps_tight_eq hi
    have h3 : B p = s := by rw [hBdef]; exact (congrArg _ hp).trans hz
    rw [h1, h2, h3]
    ring
  have hmin : IsLocalMin (fun q => B q - L q) p :=
    Filter.Eventually.of_forall (fun q => by
      change B p - L p ≤ B q - L q
      rw [hzero]
      exact hnonneg q)
  have hfd : fderiv ℝ (fun q => B q - L q) p = 0 := hmin.fderiv_eq_zero
  change fderiv ℝ (B - L) p = 0 at hfd
  rw [fderiv_sub hBdiff hLdiff] at hfd
  have hBL : fderiv ℝ B p = fderiv ℝ L p := sub_eq_zero.mp hfd
  have hconst : fderiv ℝ (fun q : ℝ × ℝ => L q - s) p = fderiv ℝ L p := fderiv_sub_const s
  rw [hconst, ← hBL]

end

end Work.Drive.Mono

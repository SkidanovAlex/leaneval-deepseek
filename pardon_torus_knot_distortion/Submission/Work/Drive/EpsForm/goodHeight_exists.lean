import Mathlib
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Drive.EpsForm.tiltedSweepGenericity_holds
import Submission.Work.Drive.Generic.ae_height_morse
import Submission.Work.Smooth.Morse.Immersion.isImmersion
import Submission.Work.Drive.EpsForm.no_crit_off_balls
import Submission.Work.Drive.EpsForm.critBranch_exists
import Submission.Work.Drive.EpsForm.hessian_inj_nhds
import Submission.Work.Drive.EpsForm.branch_pair_eventually_ne

open scoped Topology

/-!
# A good height direction near a Morse direction

Given a diffeomorphism `ψ` of `ℝ³` (the surface is `ψ` of the standard torus) and a direction `n₀`
whose height `q ↦ ⟪n₀, par ψ q⟫` has only nondegenerate critical points, we produce arbitrarily
close directions `n` whose height

* still has only nondegenerate critical points, and
* has *distinct critical values modulo the `2π`-lattice*: two critical points of the height in the
  parameter plane with the same value have the same image on the surface.

This is the general-position statement ("a generic linear height on an embedded surface is Morse with
distinct critical values") in the form the sideways sweep of Pardon's proof consumes.

The proof is by a linear perturbation `t ↦ n₀ + t • m` of the direction.  The critical points of the
height at `n₀` inside the fundamental square `[0, 2π]²` are finite (`finite_critSet_box`); by the
implicit function theorem each of them continues into a smooth branch of critical points of the
perturbed height (`critBranch_exists`), and for small `|t|` these are the only critical points in the
fundamental square (`no_crit_off_balls`) — hence, by `2π`-periodicity, the only critical points up to
lattice translation.  The critical values along the branches move with derivative equal to the
perturbing height (chain rule: `d/dt f_t(y t) = g(y t)`), so the perturbation direction `m` can be
chosen (among the finitely many forbidden hyperplanes) so that two branches with the same value at
`t = 0` separate linearly, and hence have distinct values for every small `t ≠ 0`
(`branch_pair_eventually_ne`).  Nondegeneracy is preserved by `hessian_inj_nhds`.
-/

namespace Work.Drive.EpsForm

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## The height of a direction in the parameter plane -/

/-- The height in direction `n` of the parametrised surface, read in the parameter plane. -/
def heightOf (ψ : Submission.Diffeo) (n : R3) : ℝ × ℝ → ℝ :=
  fun q => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)

theorem heightOf_eq_sweepHeight (ψ : Submission.Diffeo) (n : R3) :
    heightOf ψ n = sweepHeight ψ ((innerSL ℝ) n) := by
  funext q
  rw [heightOf, sweepHeight_innerSL]

theorem heightOf_contDiff (ψ : Submission.Diffeo) (n : R3) :
    ContDiff ℝ (⊤ : ℕ∞) (heightOf ψ n) := by
  rw [heightOf_eq_sweepHeight]
  exact Work.Smooth.Morse.pullback_contDiff ψ (ContinuousLinearMap.contDiff ((innerSL ℝ) n))

theorem heightOf_contDiff_two (ψ : Submission.Diffeo) (n : R3) :
    ContDiff ℝ 2 (heightOf ψ n) := by
  rw [heightOf_eq_sweepHeight]
  exact sweepHeight_contDiff_two ψ _

theorem heightOf_contDiff_one (ψ : Submission.Diffeo) (n : R3) :
    ContDiff ℝ 1 (heightOf ψ n) :=
  (heightOf_contDiff ψ n).of_le (by norm_num)

theorem fderiv_heightOf_periodic (ψ : Submission.Diffeo) (n : R3) (k m : ℤ) (p : ℝ × ℝ) :
    fderiv ℝ (heightOf ψ n) (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = fderiv ℝ (heightOf ψ n) p := by
  rw [heightOf_eq_sweepHeight]
  exact fderiv_sweepHeight_periodic ψ ((innerSL ℝ) n) k m p

/-- Periodicity of the derivative, for an arbitrary codomain (the file's `fderiv_periodic_add` is
stated for real-valued functions). -/
theorem fderiv_periodic_add' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {h : ℝ × ℝ → F} {c : ℝ × ℝ} (hd : ∀ q, DifferentiableAt ℝ h q)
    (hper : ∀ q, h (q + c) = h q) (p : ℝ × ℝ) : fderiv ℝ h (p + c) = fderiv ℝ h p := by
  have hf : DifferentiableAt ℝ (fun q : ℝ × ℝ => q + c) p := by fun_prop
  have hcomp := fderiv_comp (𝕜 := ℝ) (x := p) (f := fun q : ℝ × ℝ => q + c) (g := h) (hd _) hf
  have heq : h ∘ (fun q : ℝ × ℝ => q + c) = h := funext hper
  have hT : fderiv ℝ (fun q : ℝ × ℝ => q + c) p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [show (fun q : ℝ × ℝ => q + c) = (fun q => id q + c) from rfl, fderiv_add_const, fderiv_id]
  rw [heq, hT, ContinuousLinearMap.comp_id] at hcomp
  exact hcomp.symm

theorem fderiv_fderiv_heightOf_periodic (ψ : Submission.Diffeo) (n : R3) (k m : ℤ)
    (p : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (heightOf ψ n))
        (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi))
      = fderiv ℝ (fderiv ℝ (heightOf ψ n)) p := by
  have hcd : ContDiff ℝ 1 (fderiv ℝ (heightOf ψ n)) :=
    (heightOf_contDiff_two ψ n).fderiv_right (by norm_num)
  have hd : ∀ q : ℝ × ℝ, DifferentiableAt ℝ (fderiv ℝ (heightOf ψ n)) q :=
    fun q => (hcd.differentiable (by norm_num)) q
  set c : ℝ × ℝ := (-(k : ℝ) * (2 * Real.pi), -(m : ℝ) * (2 * Real.pi)) with hc
  have hper : ∀ q : ℝ × ℝ, fderiv ℝ (heightOf ψ n) (q + c) = fderiv ℝ (heightOf ψ n) q := by
    intro q
    have hkey : q + c = (q.1 - (k : ℝ) * (2 * Real.pi), q.2 - (m : ℝ) * (2 * Real.pi)) := by
      ext <;> simp [hc] <;> ring
    rw [hkey]
    exact fderiv_heightOf_periodic ψ n k m q
  have hmain := fderiv_periodic_add' hd hper p
  have hkey : p + c = (p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)) := by
    ext <;> simp [hc] <;> ring
  rw [← hkey]
  exact hmain

/-- The closed fundamental square of the `2π`-lattice. -/
def fundBox : Set (ℝ × ℝ) := Set.Icc 0 (2 * Real.pi) ×ˢ Set.Icc 0 (2 * Real.pi)

theorem isCompact_fundBox : IsCompact fundBox := isCompact_Icc.prod isCompact_Icc

/-- Every critical point of a periodic height can be moved into the fundamental square by a lattice
translation without changing its critical value, the Hessian of the height there, or its image on the
surface. -/
theorem exists_fundBox_of_crit (ψ : Submission.Diffeo) (n : R3) {p : ℝ × ℝ}
    (hp : fderiv ℝ (heightOf ψ n) p = 0) :
    ∃ p' : ℝ × ℝ, p' ∈ fundBox ∧ fderiv ℝ (heightOf ψ n) p' = 0 ∧
      heightOf ψ n p' = heightOf ψ n p ∧
      fderiv ℝ (fderiv ℝ (heightOf ψ n)) p' = fderiv ℝ (fderiv ℝ (heightOf ψ n)) p ∧
      Work.BoxShrink.Pinch.par ψ p' = Work.BoxShrink.Pinch.par ψ p := by
  obtain ⟨k, hk⟩ := exists_int_mul_two_pi p.1
  obtain ⟨m, hm⟩ := exists_int_mul_two_pi p.2
  refine ⟨(p.1 - (k : ℝ) * (2 * Real.pi), p.2 - (m : ℝ) * (2 * Real.pi)), ⟨hk, hm⟩, ?_, ?_, ?_, ?_⟩
  · rw [fderiv_heightOf_periodic]; exact hp
  · simp only [heightOf]
    rw [par_periodic]
  · exact fderiv_fderiv_heightOf_periodic ψ n k m p
  · exact par_periodic ψ k m p

/-! ## Periods of the parametrisation and of the height -/

/-- The image of a parameter point on the surface determines it up to the `2π`-lattice. -/
theorem par_eq_iff (ψ : Submission.Diffeo) (x x' : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ x = Work.BoxShrink.Pinch.par ψ x' ↔
      ∃ k m : ℤ, x.1 = x'.1 + (k : ℝ) * (2 * Real.pi) ∧
        x.2 = x'.2 + (m : ℝ) * (2 * Real.pi) := by
  constructor
  · intro h
    have h2 : Work.Core.torusMap x.1 x.2 = Work.Core.torusMap x'.1 x'.2 :=
      ψ.injective (show ψ (Work.Core.torusMap x.1 x.2) = ψ (Work.Core.torusMap x'.1 x'.2)
        from h)
    obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ := (Work.Core.torusMap_eq_iff x.1 x.2 x'.1 x'.2).mp h2
    exact ⟨k, m, hk, hm⟩
  · rintro ⟨k, m, h1, h2⟩
    show ψ (Work.Core.torusMap x.1 x.2) = ψ (Work.Core.torusMap x'.1 x'.2)
    rw [h1, h2]
    have hkey1 : x'.1 + (k : ℝ) * (2 * Real.pi) = x'.1 - ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      simp
    have hkey2 : x'.2 + (m : ℝ) * (2 * Real.pi) = x'.2 - ((-m : ℤ) : ℝ) * (2 * Real.pi) := by
      simp
    rw [hkey1, hkey2]
    exact par_periodic ψ (-k) (-m) x'

/-- The parametrisation is invariant under translations of the `2π`-lattice. -/
theorem par_add_shift (ψ : Submission.Diffeo) (K M : ℤ) (q : ℝ × ℝ) :
    Work.BoxShrink.Pinch.par ψ (q + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)))
      = Work.BoxShrink.Pinch.par ψ q := by
  have h := par_periodic ψ (-K) (-M) q
  have hkey : (q.1 - ((-K : ℤ) : ℝ) * (2 * Real.pi), q.2 - ((-M : ℤ) : ℝ) * (2 * Real.pi))
      = q + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi)) := by
    ext <;> simp
  rwa [hkey] at h

/-- The height is invariant under translations of the `2π`-lattice. -/
theorem heightOf_add_shift (ψ : Submission.Diffeo) (n : R3) (K M : ℤ) (q : ℝ × ℝ) :
    heightOf ψ n (q + ((K : ℝ) * (2 * Real.pi), (M : ℝ) * (2 * Real.pi))) = heightOf ψ n q := by
  simp only [heightOf]
  rw [par_add_shift]

/-! ## A direction avoiding finitely many hyperplanes -/

/-- Given finitely many nonzero vectors, there is a nonzero vector whose inner product with each of
them is nonzero. -/
theorem exists_m_inner_ne_zero (W : Finset R3) (hW : ∀ w ∈ W, w ≠ 0) :
    ∃ m : R3, m ≠ 0 ∧ ∀ w ∈ W, inner ℝ m w ≠ 0 := by
  classical
  rcases W.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨c₀, hc₀⟩ := exists_ne (0 : R3)
    exact ⟨c₀, hc₀, by simp⟩
  · let f : ↥W → Module.Dual ℝ R3 := fun w => (innerSL ℝ) (w : R3)
    have hf : ∀ i : ↥W, ∃ x : R3, f i x ≠ 0 := by
      intro i
      refine ⟨(i : R3), ?_⟩
      show ((innerSL ℝ) (i : R3)) (i : R3) ≠ 0
      rw [innerSL_apply_apply]
      exact inner_self_eq_zero.not.mpr (hW i i.2)
    obtain ⟨m, hm⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
    refine ⟨m, ?_, fun w hw => ?_⟩
    · obtain ⟨w₀, hw₀⟩ := hne
      have h1 : f ⟨w₀, hw₀⟩ m ≠ 0 := hm ⟨w₀, hw₀⟩
      intro h0
      rw [h0] at h1
      simp at h1
    · have h1 : f ⟨w, hw⟩ m ≠ 0 := hm ⟨w, hw⟩
      show inner ℝ m w ≠ 0
      have h2 : ((innerSL ℝ) (w : R3)) m ≠ 0 := h1
      rw [innerSL_apply_apply] at h2
      simpa only [real_inner_comm] using h2

/-! ## Combining finitely many eventual statements -/

theorem eventually_forall_mem_finset {α β : Type*} {l : Filter β} {s : Finset α}
    {p : α → β → Prop} (h : ∀ a ∈ s, ∀ᶠ x in l, p a x) :
    ∀ᶠ x in l, ∀ a ∈ s, p a x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha' : ∀ᶠ x in l, p a x := h a (Finset.mem_insert_self a s)
      have hs' : ∀ b ∈ s, ∀ᶠ x in l, p b x := fun b hb => h b (Finset.mem_insert_of_mem hb)
      filter_upwards [ha', ih hs'] with x h1 h2 b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact h1
      · exact h2 b hb






/-! ## The main statement -/

theorem goodHeight_exists (ψ : Submission.Diffeo) (n₀ : LeanEval.KnotTheory.PardonDistortion.R3) (ρ : ℝ) (hρ : 0 < ρ)
    (hn₀ : ∀ p : ℝ × ℝ,
      fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
      Function.Injective
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n₀ (Work.BoxShrink.Pinch.par ψ q))) p)) :
    ∃ n ∈ Metric.ball n₀ ρ,
      (∀ p : ℝ × ℝ,
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        Function.Injective
          (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q))) p)) ∧
      (∀ p p' : ℝ × ℝ,
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p = 0 →
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ n (Work.BoxShrink.Pinch.par ψ q)) p' = 0 →
        inner ℝ n (Work.BoxShrink.Pinch.par ψ p) = inner ℝ n (Work.BoxShrink.Pinch.par ψ p') →
        Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p') := by
  classical
  -- ## 1. the critical points of the height at `n₀` inside the fundamental square
  have hnd₀ : ∀ p : ℝ × ℝ, fderiv ℝ (heightOf ψ n₀) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (heightOf ψ n₀)) p) := fun p hp => hn₀ p hp
  have hfin : ({p : ℝ × ℝ | fderiv ℝ (heightOf ψ n₀) p = 0} ∩ fundBox).Finite := by
    simpa only [fundBox] using finite_critSet_box (heightOf_contDiff_two ψ n₀) hnd₀
  obtain ⟨X, hX⟩ : ∃ X : Finset (ℝ × ℝ),
      ∀ p, p ∈ X ↔ fderiv ℝ (heightOf ψ n₀) p = 0 ∧ p ∈ fundBox :=
    ⟨hfin.toFinset, fun p => by
      rw [Set.Finite.mem_toFinset]
      exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩⟩
  -- ## 2. the perturbation direction
  set P : Finset ((ℝ × ℝ) × (ℝ × ℝ)) :=
    (X.product X).filter (fun z => Work.BoxShrink.Pinch.par ψ z.1 ≠ Work.BoxShrink.Pinch.par ψ z.2)
    with hPdef
  set W : Finset R3 :=
    P.image (fun z => Work.BoxShrink.Pinch.par ψ z.1 - Work.BoxShrink.Pinch.par ψ z.2) with hWdef
  have hWne : ∀ w ∈ W, w ≠ 0 := by
    intro w hw
    rw [hWdef, Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hz).2
  obtain ⟨m, hm0, hmne⟩ := exists_m_inner_ne_zero W hWne
  have hmgood : ∀ x ∈ X, ∀ x' ∈ X, Work.BoxShrink.Pinch.par ψ x ≠ Work.BoxShrink.Pinch.par ψ x' →
      inner ℝ m (Work.BoxShrink.Pinch.par ψ x - Work.BoxShrink.Pinch.par ψ x') ≠ 0 := by
    intro x hx x' hx' hne
    have hmem : (x, x') ∈ P := by
      rw [hPdef, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hx, hx'⟩, hne⟩
    exact hmne _ (by rw [hWdef]; exact Finset.mem_image.mpr ⟨(x, x'), hmem, rfl⟩)
  -- ## 3. the branches of critical points and the three uniformity radii
  have hXnd : ∀ x ∈ X, fderiv ℝ (heightOf ψ n₀) x = 0 ∧
      Function.Injective (fderiv ℝ (fderiv ℝ (heightOf ψ n₀)) x) :=
    fun x hx => ⟨((hX x).mp hx).1, hnd₀ x ((hX x).mp hx).1⟩
  obtain ⟨y, δb, rb, C, hδb, hrb, hC, hy0, hycrit, hyuniq, hyLip⟩ :=
    critBranch_exists (heightOf_contDiff_two ψ n₀) (heightOf_contDiff_two ψ m) X hXnd
  obtain ⟨δh, hδh, hhess⟩ :=
    hessian_inj_nhds (heightOf_contDiff_two ψ n₀) (heightOf_contDiff_two ψ m) X
      (fun x hx => (hXnd x hx).2)
  obtain ⟨δc, hδc, hnocrit⟩ :=
    no_crit_off_balls (heightOf_contDiff_two ψ n₀) (heightOf_contDiff_two ψ m)
      isCompact_fundBox X (fun p hp hcrit => (hX p).mpr ⟨hcrit, hp⟩) hrb
  -- ## 4. the pair condition
  have hpairEv : ∀ z ∈ P, ∀ᶠ t in 𝓝[>] (0 : ℝ),
      heightOf ψ n₀ (y z.1 t) + t * heightOf ψ m (y z.1 t) ≠
        heightOf ψ n₀ (y z.2 t) + t * heightOf ψ m (y z.2 t) := by
    intro z hz
    obtain ⟨hzX, hzpar⟩ := Finset.mem_filter.mp hz
    obtain ⟨hz1, hz2⟩ := Finset.mem_product.mp hzX
    have hz1crit : fderiv ℝ (heightOf ψ n₀) z.1 = 0 := ((hX z.1).mp hz1).1
    have hz2crit : fderiv ℝ (heightOf ψ n₀) z.2 = 0 := ((hX z.2).mp hz2).1
    have hGne : heightOf ψ m z.1 ≠ heightOf ψ m z.2 := by
      intro h1
      refine hmgood z.1 hz1 z.2 hz2 hzpar ?_
      have h2 : heightOf ψ m z.1 - heightOf ψ m z.2 = 0 := sub_eq_zero.mpr h1
      have h3 : heightOf ψ m z.1 - heightOf ψ m z.2 =
          inner ℝ m (Work.BoxShrink.Pinch.par ψ z.1 - Work.BoxShrink.Pinch.par ψ z.2) := by
        simp only [heightOf, inner_sub_right]
      rwa [h3] at h2
    refine branch_pair_eventually_ne (heightOf ψ n₀) (heightOf ψ m)
      (heightOf_contDiff_one ψ n₀) (heightOf_contDiff_one ψ m) hz1crit hz2crit hδb hC
      (hyLip z.1 hz1) (hyLip z.2 hz2) ?_
    rcases eq_or_ne (heightOf ψ n₀ z.1) (heightOf ψ n₀ z.2) with h | h
    · exact Or.inr hGne
    · exact Or.inl h
  have hAllPairs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ P,
      heightOf ψ n₀ (y z.1 t) + t * heightOf ψ m (y z.1 t) ≠
        heightOf ψ n₀ (y z.2 t) + t * heightOf ψ m (y z.2 t) :=
    eventually_forall_mem_finset hpairEv
  -- ## 5. choose a small positive `t`
  have hbig : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t * ‖m‖ < ρ ∧ (C + 1) * |t| < min δh rb ∧ |t| < δb ∧ |t| < δc ∧
      (∀ z ∈ P, heightOf ψ n₀ (y z.1 t) + t * heightOf ψ m (y z.1 t) ≠
        heightOf ψ n₀ (y z.2 t) + t * heightOf ψ m (y z.2 t)) := by
    have h1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t * ‖m‖ < ρ :=
      (((continuous_id.mul continuous_const).continuousAt.tendsto).mono_left
        nhdsWithin_le_nhds).eventually (eventually_lt_nhds (by simpa using hρ))
    have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), (C + 1) * |t| < min δh rb := by
      have hpos : 0 < min δh rb / (C + 1) :=
        div_pos (lt_min hδh hrb) (by linarith)
      filter_upwards [Ioo_mem_nhdsGT hpos] with t ht
      rw [abs_of_pos ht.1]
      calc (C + 1) * t < (C + 1) * (min δh rb / (C + 1)) :=
            mul_lt_mul_of_pos_left ht.2 (by linarith)
        _ = min δh rb := by
            rw [mul_comm (C + 1)]
            exact div_mul_cancel₀ _ (by linarith)
    have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), |t| < δb := by
      filter_upwards [Ioo_mem_nhdsGT hδb] with t ht
      rw [abs_of_pos ht.1]; exact ht.2
    have h4 : ∀ᶠ t in 𝓝[>] (0 : ℝ), |t| < δc := by
      filter_upwards [Ioo_mem_nhdsGT hδc] with t ht
      rw [abs_of_pos ht.1]; exact ht.2
    filter_upwards [h1, h2, h3, h4, hAllPairs] with t h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ε, hε, hεsub⟩ := (nhdsGT_basis (0 : ℝ)).mem_iff.mp hbig
  set t : ℝ := ε / 2 with htdef
  have htpos : 0 < t := by rw [htdef]; linarith
  have htmem : t ∈ Set.Ioo 0 ε := ⟨htpos, by rw [htdef]; linarith⟩
  obtain ⟨htρ, htC, htb, htc, htpairs⟩ := hεsub htmem
  have htabs : 0 < |t| := abs_pos.mpr (ne_of_gt htpos)
  have htmin : |t| < min δh rb := by
    have h3 : |t| ≤ (C + 1) * |t| := by nlinarith [hC, htabs]
    linarith
  have htCs : C * |t| < δh ∧ C * |t| < rb := by
    have h3 : C * |t| < (C + 1) * |t| := by nlinarith [hC, htabs]
    have h4 : C * |t| < min δh rb := lt_trans h3 htC
    exact ⟨lt_of_lt_of_le h4 (min_le_left _ _), lt_of_lt_of_le h4 (min_le_right _ _)⟩
  -- ## 6. the linear form of the perturbed height
  have hlin : heightOf ψ (n₀ + t • m) = fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q := by
    funext q
    simp only [heightOf]
    rw [inner_add_left, real_inner_smul_left]
  have hlin2 : (fun q : ℝ × ℝ => inner ℝ (n₀ + t • m) (Work.BoxShrink.Pinch.par ψ q)) =
      fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q := hlin
  -- ## 7. conclusion
  refine ⟨n₀ + t • m, ?_, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have hsub : n₀ + t • m - n₀ = t • m := by abel
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
    exact htρ
  · -- the Morse property
    intro p hp
    obtain ⟨p', hp'box, hp'crit, -, hp'hess, -⟩ := exists_fundBox_of_crit ψ (n₀ + t • m) hp
    rw [hlin] at hp'crit hp'hess
    rw [hlin2]
    obtain ⟨x, hxX, hxdist⟩ := hnocrit t htc p' hp'box hp'crit
    have hp'eq : p' = y x t := hyuniq x hxX t htb p' hxdist hp'crit
    have hinj : Function.Injective
        (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q)) (y x t)) :=
      hhess x hxX t (lt_of_lt_of_le htmin (min_le_left _ _))
        (y x t) (lt_of_le_of_lt (hyLip x hxX t htb) htCs.1)
    rw [← hp'eq] at hinj
    rw [hp'hess] at hinj
    exact hinj
  · -- the distinctness of critical values
    intro p p' hp hp' hval
    obtain ⟨p₁, hp₁box, hp₁crit, hp₁val, -, hp₁par⟩ := exists_fundBox_of_crit ψ (n₀ + t • m) hp
    obtain ⟨p₂, hp₂box, hp₂crit, hp₂val, -, hp₂par⟩ := exists_fundBox_of_crit ψ (n₀ + t • m) hp'
    have hvalH : heightOf ψ (n₀ + t • m) p = heightOf ψ (n₀ + t • m) p' := hval
    rw [hlin] at hp₁crit hp₁val hp₂crit hp₂val hvalH
    obtain ⟨x, hxX, hxdist⟩ := hnocrit t htc p₁ hp₁box hp₁crit
    have hp₁eq : p₁ = y x t := hyuniq x hxX t htb p₁ hxdist hp₁crit
    obtain ⟨x', hx'X, hx'dist⟩ := hnocrit t htc p₂ hp₂box hp₂crit
    have hp₂eq : p₂ = y x' t := hyuniq x' hx'X t htb p₂ hx'dist hp₂crit
    have hFV : heightOf ψ n₀ (y x t) + t * heightOf ψ m (y x t) =
        heightOf ψ n₀ (y x' t) + t * heightOf ψ m (y x' t) := by
      have h1 := hvalH
      rw [← hp₁val, ← hp₂val] at h1
      rw [hp₁eq, hp₂eq] at h1
      exact h1
    rcases eq_or_ne (Work.BoxShrink.Pinch.par ψ x) (Work.BoxShrink.Pinch.par ψ x') with hpar | hpar
    · -- same image on the surface: the two branches are lattice translates of each other
      obtain ⟨k, m', hk, hm'⟩ := (par_eq_iff ψ x x').mp hpar
      set c : ℝ × ℝ := (((-k : ℤ) : ℝ) * (2 * Real.pi), ((-m' : ℤ) : ℝ) * (2 * Real.pi)) with hcdef
      have hx'eq : x' = x + c := by
        have h1 : x'.1 = x.1 + (((-k : ℤ) : ℝ) * (2 * Real.pi)) := by
          push_cast
          linarith
        have h2 : x'.2 = x.2 + (((-m' : ℤ) : ℝ) * (2 * Real.pi)) := by
          push_cast
          linarith
        ext
        · simpa [hcdef] using h1
        · simpa [hcdef] using h2
      have hparc : ∀ q : ℝ × ℝ,
          Work.BoxShrink.Pinch.par ψ (q + c) = Work.BoxShrink.Pinch.par ψ q := by
        intro q
        rw [hcdef]
        exact par_add_shift ψ (-k) (-m') q
      have hdist : ‖y x t + c - x'‖ < rb := by
        have h4 : y x t + c - x' = y x t - x := by rw [hx'eq]; abel
        rw [h4]
        exact lt_of_le_of_lt (hyLip x hxX t htb) htCs.2
      have hcritshift : fderiv ℝ (fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q)
          (y x t + c) = 0 := by
        have hper : ∀ q : ℝ × ℝ,
            (fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q) (q + c)
              = (fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q) q := by
          intro q
          rw [hcdef]
          simp only []
          rw [heightOf_add_shift ψ n₀ (-k) (-m') q, heightOf_add_shift ψ m (-k) (-m') q]
        have hd : ∀ q : ℝ × ℝ,
            DifferentiableAt ℝ (fun q : ℝ × ℝ => heightOf ψ n₀ q + t * heightOf ψ m q) q := by
          intro q
          have h0 : DifferentiableAt ℝ (heightOf ψ n₀) q :=
            ((heightOf_contDiff ψ n₀).differentiable (by simp)).differentiableAt
          have h1 : DifferentiableAt ℝ (heightOf ψ m) q :=
            ((heightOf_contDiff ψ m).differentiable (by simp)).differentiableAt
          exact h0.add (h1.const_mul t)
        rw [fderiv_periodic_add' hd hper (y x t)]
        exact hycrit x hxX t htb
      have huniq := hyuniq x' hx'X t htb (y x t + c) hdist hcritshift
      have hstep : Work.BoxShrink.Pinch.par ψ (y x t) = Work.BoxShrink.Pinch.par ψ (y x' t) := by
        rw [← huniq]
        exact (hparc (y x t)).symm
      rw [← hp₁par, ← hp₂par, hp₁eq, hp₂eq]
      exact hstep
    · -- distinct images on the surface: the pair condition separates the values
      have hmemP : (x, x') ∈ P := by
        rw [hPdef, Finset.mem_filter]
        exact ⟨Finset.mem_product.mpr ⟨hxX, hx'X⟩, hpar⟩
      exact absurd hFV (htpairs (x, x') hmemP)

end

end Work.Drive.EpsForm

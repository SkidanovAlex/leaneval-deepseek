import Mathlib
import Submission.Work.Drive.EpsFormSphere.Sideways

namespace Work.Drive.EpsFormSphere

/-- A nonempty open order-convex subset of `ℝ` which is bounded above and below is the open
interval between its infimum and its supremum. -/
private lemma eq_Ioo_sInf_sSup_of_isOpen_ordConnected {S : Set ℝ} (hne : S.Nonempty)
    (hbb : BddBelow S) (hba : BddAbove S) (hopen : IsOpen S) (hord : S.OrdConnected) :
    S = Set.Ioo (sInf S) (sSup S) := by
  ext x
  constructor
  · intro hx
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen x hx
    have h1 : x - ε / 2 ∈ S := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have : x - ε / 2 - x = -(ε / 2) := by ring
      rw [this, abs_neg, abs_of_pos (by linarith)]
      linarith
    have h2 : x + ε / 2 ∈ S := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq]
      have : x + ε / 2 - x = ε / 2 := by ring
      rw [this, abs_of_pos (by linarith)]
      linarith
    exact ⟨lt_of_le_of_lt (csInf_le hbb h1) (by linarith),
      lt_of_lt_of_le (by linarith) (le_csSup hba h2)⟩
  · intro hx
    obtain ⟨y, hyS, hyx⟩ : ∃ y ∈ S, y < x := by
      by_contra hcon
      push Not at hcon
      have := le_csInf hne hcon
      linarith [hx.1]
    obtain ⟨z, hzS, hxz⟩ : ∃ z ∈ S, x < z := by
      by_contra hcon
      push Not at hcon
      have := csSup_le hne hcon
      linarith [hx.2]
    exact hord.out hyS hzS ⟨hyx.le, hxz.le⟩

open LeanEval.KnotTheory.PardonDistortion in
/-- **A crossing of the cutting plane is a single short arc of the slab.**

`K` is a smooth knot, `t₀` a parameter at which `K` crosses the cutting plane
`{y : y (σ 2) = c (σ 2) + u}` transversally, and both the level coordinate `y ↦ y (σ 2)` and the
sweeping functional `ℓ` of the sideways slab are *increasing* in the parameter at that crossing.  Then
for a small enough slab half-width `h` the parameters near `t₀` at which the knot lies in the slab
`slabZ c σ u h = {y : |y (σ 2) - (c (σ 2) + u)| < h}` form an interval around `t₀`, on which `y ↦ y (σ 2)`
and `ℓ` are both strictly increasing.

This is the local core of the slab count of Pardon's `doublebubble2`: every crossing of the cutting
plane contributes exactly one short arc of the knot inside the slab, the arc crosses the slab from one
face to the other, and it meets the wall `{ℓ = lam}` at most once; summing over the finitely many
crossings (counted by the crux's second hypothesis) gives
`#(K ∩ ∂R_lam) ≤ #(K ∩ ∂PBox) + 2 #(K ∩ D) < min p q` for the swept ball
`R_lam = PBox \ (slabZ ∩ {ℓ < lam})`, which is the count at the regular level.

(The two positivity hypotheses are the orientation choice of the sweep; a knot with the opposite
orientations at the crossing satisfies the same statement after replacing `t` by `-t` and `ℓ` by `-ℓ`,
which is how the consumer applies it.) -/
theorem slabArc_of_crossing {K : Knot} {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {t₀ : ℝ}
    (hlevel : K.curve t₀ (σ 2) = c (σ 2) + u)
    (hplane : 0 < (deriv K.curve t₀) (σ 2))
    (hwall : 0 < ℓ (deriv K.curve t₀)) :
    ∃ δ h₀ : ℝ, 0 < δ ∧ 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h < h₀ →
      (∃ a b : ℝ, a < t₀ ∧ t₀ < b ∧
        {t : ℝ | |t - t₀| < δ ∧ K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h} = Set.Ioo a b) ∧
      (∀ s ∈ {t : ℝ | |t - t₀| < δ ∧ K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h},
       ∀ t ∈ {t : ℝ | |t - t₀| < δ ∧ K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h}, s < t →
         K.curve s (σ 2) < K.curve t (σ 2) ∧ ℓ (K.curve s) < ℓ (K.curve t)) := by
  have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) K.curve := K.smooth
  have hdiff : ∀ t : ℝ, HasDerivAt K.curve (deriv K.curve t) t := fun t =>
    ((K.smooth.differentiable (by simp)) t).hasDerivAt
  -- the derivative of the level coordinate and of `ℓ` along the curve
  have hderiv_coord : deriv (fun t : ℝ => K.curve t (σ 2)) t₀ = (deriv K.curve t₀) (σ 2) :=
    ((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ 2)).hasFDerivAt.comp_hasDerivAt t₀
      (hdiff t₀)).deriv
  have hderiv_g : deriv (fun t : ℝ => ℓ (K.curve t)) t₀ = ℓ (deriv K.curve t₀) :=
    (ℓ.hasFDerivAt.comp_hasDerivAt t₀ (hdiff t₀)).deriv
  have hlevel_cont : Continuous fun t : ℝ => K.curve t (σ 2) :=
    (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ 2)).continuous.comp hsm.continuous
  have hg_cont : Continuous fun t : ℝ => ℓ (K.curve t) := ℓ.continuous.comp hsm.continuous
  -- both derivatives are continuous (the knot is `C^∞`)
  have hcont_f : Continuous (deriv (fun t : ℝ => K.curve t (σ 2))) := by
    have hc : Continuous (fun t : ℝ => (deriv K.curve t) (σ 2)) :=
      (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ 2)).continuous.comp
        (hsm.continuous_deriv (by simp))
    exact hc.congr fun t =>
      (((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (σ 2)).hasFDerivAt.comp_hasDerivAt t
        (hdiff t)).deriv).symm
  have hcont_g : Continuous (deriv (fun t : ℝ => ℓ (K.curve t))) :=
    (ℓ.continuous.comp (hsm.continuous_deriv (by simp))).congr fun t =>
      ((ℓ.hasFDerivAt.comp_hasDerivAt t (hdiff t)).deriv).symm
  -- the two derivatives are positive at `t₀`
  have hpos_f : 0 < deriv (fun t : ℝ => K.curve t (σ 2)) t₀ := by
    rw [hderiv_coord]; exact hplane
  have hpos_g : 0 < deriv (fun t : ℝ => ℓ (K.curve t)) t₀ := by
    rw [hderiv_g]; exact hwall
  -- hence both are positive on a common ball
  have h1ev : ∀ᶠ t in nhds t₀, 0 < deriv (fun t : ℝ => K.curve t (σ 2)) t :=
    (isOpen_lt continuous_const hcont_f).mem_nhds hpos_f
  have h2ev : ∀ᶠ t in nhds t₀, 0 < deriv (fun t : ℝ => ℓ (K.curve t)) t :=
    (isOpen_lt continuous_const hcont_g).mem_nhds hpos_g
  obtain ⟨δ, hδpos, hδball⟩ := Metric.mem_nhds_iff.mp (h1ev.and h2ev)
  have hδ : ∀ t : ℝ, dist t t₀ < δ →
      0 < deriv (fun t : ℝ => K.curve t (σ 2)) t ∧ 0 < deriv (fun t : ℝ => ℓ (K.curve t)) t :=
    fun t ht => hδball (by simpa [Metric.mem_ball] using ht)
  -- `y ↦ y (σ 2)` and `ℓ` are strictly increasing on the ball
  have hmono_level : StrictMonoOn (fun t : ℝ => K.curve t (σ 2)) (Set.Ioo (t₀ - δ) (t₀ + δ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hlevel_cont.continuousOn ?_
    intro x hx
    rw [interior_Ioo] at hx
    exact (hδ x (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)).1
  have hmono_g : StrictMonoOn (fun t : ℝ => ℓ (K.curve t)) (Set.Ioo (t₀ - δ) (t₀ + δ)) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioo _ _) hg_cont.continuousOn ?_
    intro x hx
    rw [interior_Ioo] at hx
    exact (hδ x (by rw [Real.dist_eq, abs_lt]; exact ⟨by linarith [hx.1], by linarith [hx.2]⟩)).2
  refine ⟨δ, 1, hδpos, one_pos, ?_⟩
  intro h hh _
  set S : Set ℝ := {t : ℝ | |t - t₀| < δ ∧ K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h}
    with hSdef
  have hfmem : ∀ t : ℝ, t ∈ S ↔ |t - t₀| < δ ∧ |K.curve t (σ 2) - (c (σ 2) + u)| < h := by
    intro t
    simp only [hSdef, Work.Drive.EpsSphere.slabZ, Set.mem_ofPred_eq]
  have hsub : ∀ t ∈ S, t ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := by
    intro t ht
    have h1 := ((hfmem t).mp ht).1
    rw [abs_lt] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hbddBelow : BddBelow S := ⟨t₀ - δ, fun t ht => (hsub t ht).1.le⟩
  have hbddAbove : BddAbove S := ⟨t₀ + δ, fun t ht => (hsub t ht).2.le⟩
  have ht₀S : t₀ ∈ S := by
    rw [hfmem t₀]
    exact ⟨by simpa using hδpos, by rw [hlevel, sub_self, abs_zero]; exact hh⟩
  have hne : S.Nonempty := ⟨t₀, ht₀S⟩
  -- `S` is open
  have hopen : IsOpen S := by
    rw [hSdef]
    have h1 : IsOpen {t : ℝ | |t - t₀| < δ} := by
      simpa using
        isOpen_lt ((continuous_id.sub continuous_const).abs) (continuous_const : Continuous fun _ : ℝ => δ)
    have h2 : IsOpen {t : ℝ | K.curve t ∈ Work.Drive.EpsSphere.slabZ c σ u h} := by
      simp only [Work.Drive.EpsSphere.slabZ, Set.mem_ofPred_eq]
      exact isOpen_lt ((hlevel_cont.sub continuous_const).abs) continuous_const
    rw [Set.ofPred_and]
    exact h1.inter h2
  -- `S` is order connected (a sublevel set of the strictly increasing level coordinate)
  have hord : S.OrdConnected := by
    refine Set.ordConnected_of_Ioo ?_
    intro x hx y hy hxy z hz
    have hx' := (hfmem x).mp hx
    have hy' := (hfmem y).mp hy
    have hzδ : |z - t₀| < δ := by
      have hxδ := hx'.1
      have hyδ := hy'.1
      rw [abs_lt] at hxδ hyδ ⊢
      exact ⟨by linarith [hz.1, hxδ.1], by linarith [hz.2, hyδ.2]⟩
    have hzf : |K.curve z (σ 2) - (c (σ 2) + u)| < h := by
      have hxm : x ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := hsub x hx
      have hym : y ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := hsub y hy
      have hzm : z ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := by
        rw [abs_lt] at hzδ
        exact ⟨by linarith [hzδ.1], by linarith [hzδ.2]⟩
      have hln : K.curve x (σ 2) < K.curve z (σ 2) := hmono_level hxm hzm (by linarith [hz.1])
      have hln' : K.curve z (σ 2) < K.curve y (σ 2) := hmono_level hzm hym (by linarith [hz.2])
      have hx2 := abs_lt.mp hx'.2
      have hy2 := abs_lt.mp hy'.2
      rw [abs_lt]
      exact ⟨by linarith [hx2.1], by linarith [hy2.2]⟩
    exact (hfmem z).mpr ⟨hzδ, hzf⟩
  obtain heq : S = Set.Ioo (sInf S) (sSup S) :=
    eq_Ioo_sInf_sSup_of_isOpen_ordConnected hne hbddBelow hbddAbove hopen hord
  constructor
  · exact ⟨sInf S, sSup S, (heq ▸ ht₀S).1, (heq ▸ ht₀S).2, heq⟩
  · intro s hs t ht hst
    have hsm' : s ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := hsub s hs
    have htm' : t ∈ Set.Ioo (t₀ - δ) (t₀ + δ) := hsub t ht
    exact ⟨hmono_level hsm' htm' hst, hmono_g hsm' htm' hst⟩

end Work.Drive.EpsFormSphere

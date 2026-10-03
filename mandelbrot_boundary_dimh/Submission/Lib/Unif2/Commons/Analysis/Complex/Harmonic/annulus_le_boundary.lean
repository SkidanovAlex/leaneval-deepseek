import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.HarmonicContOnCl
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.MeanValue
import Submission.Lib.Unif2.Commons.Analysis.Complex.exp_I_mul_eq_of_norm_one

open Set Metric Complex InnerProductSpace Filter
open scoped Topology Real



namespace Commons.Analysis.Complex.Harmonic


private lemma harmonic_eqOn_nhds_of_le {u : ℂ → ℝ} {q : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hu : HarmonicOnNhd u (ball q ε)) (hle : ∀ y ∈ ball q ε, u y ≤ u q) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y ∈ ball q δ, u y = u q := by
  classical
  obtain ⟨F, hFa, hFe⟩ := InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq hu
  let g : ℂ → ℂ := fun z => Complex.exp (F z)
  have hnorm : ∀ y ∈ ball q ε, ‖g y‖ = Real.exp (u y) := by
    intro y hy
    dsimp [g]
    rw [Complex.norm_exp]
    congr 1
    exact hFe hy
  have hloc : IsLocalMax (norm ∘ g) q := by
    show ∀ᶠ y in 𝓝 q, ‖g y‖ ≤ ‖g q‖
    exact eventually_of_mem (ball_mem_nhds q hε) (by
      intro y hy
      rw [hnorm y hy, hnorm q (mem_ball_self hε)]
      exact (Real.exp_le_exp).2 (hle y hy))
  have hdiff : ∀ᶠ z in 𝓝 q, DifferentiableAt ℂ g z := by
    filter_upwards [ball_mem_nhds q hε] with z hz
    dsimp [g]
    exact Complex.differentiable_exp.differentiableAt.comp z ((hFa z hz).differentiableAt)
  have hEq : ∀ᶠ y in 𝓝 q, ‖g y‖ = ‖g q‖ :=
    Complex.norm_eventually_eq_of_isLocalMax (f := g) (c := q) hdiff hloc
  have hEqAnd : ∀ᶠ y in 𝓝 q, ‖g y‖ = ‖g q‖ ∧ y ∈ ball q ε := hEq.and (ball_mem_nhds q hε)
  rcases Metric.eventually_nhds_iff.mp hEqAnd with ⟨δ, hδ0, hδ⟩
  refine ⟨δ, hδ0, ?_⟩
  intro y hy
  have hnormEq : ‖g y‖ = ‖g q‖ := (hδ hy).1
  have hyB : y ∈ ball q ε := (hδ hy).2
  have he : Real.exp (u y) = Real.exp (u q) := by
    exact (hnorm y hyB).symm.trans (hnormEq.trans (hnorm q (mem_ball_self hε)))
  exact Real.exp_injective he


private lemma harmonic_eqOn_of_isMaxOn {A : Set ℂ} (hAopen : IsOpen A) (hApre : IsPreconnected A)
    {u : ℂ → ℝ} (hu : HarmonicOnNhd u A) {c : ℂ} (hcA : c ∈ A) (hm : IsMaxOn u A c) :
    ∀ z ∈ A, u z = u c := by
  classical
  set V : Set ℂ := A ∩ {z | IsMaxOn u A z}
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    rcases hz with ⟨hzA, hzMax⟩
    rcases isOpen_iff.1 hAopen z hzA with ⟨ε, hε0, hball⟩
    have hle : ∀ y ∈ ball z ε, u y ≤ u z := fun y hy => hzMax (hball hy)
    obtain ⟨δ, hδ0, hδ⟩ := harmonic_eqOn_nhds_of_le (q := z) (ε := ε) hε0 (hu.mono hball) hle
    let δ' := min δ ε
    have hδ'pos : 0 < δ' := lt_min hδ0 hε0
    refine mem_of_superset (ball_mem_nhds z hδ'pos) ?_
    intro y hy
    have hyδ : y ∈ ball z δ := Metric.ball_subset_ball (min_le_left δ ε) hy
    have hyε : y ∈ ball z ε := Metric.ball_subset_ball (min_le_right δ ε) hy
    refine ⟨hball hyε, ?_⟩
    intro x hxA
    rw [hδ y hyδ]
    exact hzMax hxA
  set W : Set ℂ := A ∩ {z | u z < u c}
  have hWopen : IsOpen W := by
    have ht : IsOpen {y : ℝ | y < u c} := isOpen_lt continuous_id continuous_const
    simpa [W] using hu.continuousOn.isOpen_inter_preimage hAopen ht
  have hdisj : Disjoint V W := by
    rw [disjoint_iff_inf_le]
    intro x hx
    rcases hx with ⟨⟨hxA, hxMax⟩, ⟨_, hxlt⟩⟩
    change u x < u c at hxlt
    exact (not_le_of_gt hxlt) (hxMax hcA)
  have hAVW : A ⊆ V ∪ W := by
    intro x hxA
    by_cases hxu : u x = u c
    · left
      refine ⟨hxA, ?_⟩
      intro y hy
      rw [hxu]
      exact hm hy
    · right
      refine ⟨hxA, ?_⟩
      exact lt_of_le_of_ne (hm hxA) hxu
  have hAnon : (A ∩ V).Nonempty := ⟨c, hcA, hcA, hm⟩
  have hsub : A ⊆ V := IsPreconnected.subset_left_of_subset_union (s := A) (u := V) (v := W)
    hVopen hWopen hdisj hAVW hAnon hApre
  intro z hz
  rcases hsub hz with ⟨_, hzMax⟩
  exact le_antisymm (hm hz) (hzMax hcA)

private lemma cexp_mul_I_norm_one (t : ℝ) : ‖Complex.exp (t * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

private lemma norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]


private lemma preconnected_annulus {r R : ℝ} (hr : 0 < r) (_hrR : r < R) :
    IsPreconnected {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} := by
  let S : Set (ℝ × ℝ) := Set.Ioo r R ×ˢ (Set.univ : Set ℝ)
  let F : ℝ × ℝ → ℂ := fun x => (x.1 : ℂ) * Complex.exp (x.2 * Complex.I)
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hSpre : IsPreconnected S :=
    IsPreconnected.prod isPreconnected_Ioo (PreconnectedSpace.isPreconnected_univ (α := ℝ))
  have himg : IsPreconnected (F '' S) := IsPreconnected.image hSpre F hFcont.continuousOn
  have him_forward : F '' S ⊆ {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} := by
    intro z hz
    rcases hz with ⟨x, hxS, rfl⟩
    rcases hxS with ⟨hx1, _⟩
    have h1 : r < x.1 := hx1.1
    have h2 : x.1 < R := hx1.2
    have hx1pos : 0 < x.1 := lt_trans hr h1
    have hnorm : ‖F x‖ = x.1 := by
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx1pos, cexp_mul_I_norm_one]
      ring
    change r < ‖F x‖ ∧ ‖F x‖ < R
    rw [hnorm]
    exact ⟨h1, h2⟩
  have him_backward : {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} ⊆ F '' S := by
    intro z hz
    rcases hz with ⟨hz1, hz2⟩
    have hzpos : 0 < ‖z‖ := lt_trans hr hz1
    have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
    have hzn0 : ‖z‖ ≠ 0 := ne_of_gt hzpos
    have hw1 : ‖z / (‖z‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
      exact div_self hzn0
    obtain ⟨σ, hσ⟩ := Commons.Analysis.Complex.exp_I_mul_eq_of_norm_one (w := z / (‖z‖ : ℂ)) hw1
    refine ⟨(‖z‖, σ), ⟨⟨hz1, hz2⟩, trivial⟩, ?_⟩
    dsimp [F]
    rw [hσ]
    have hc0 : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hzn0
    field_simp [hc0]
  have him : F '' S = {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} :=
    le_antisymm him_forward him_backward
  rw [← him]
  exact himg
private lemma isOpen_annulus {r R : ℝ} : IsOpen {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} := by
  have h1 : IsOpen {z : ℂ | r < ‖z‖} := by
    simpa using
      (isOpen_lt (f := fun _ : ℂ => r) (g := fun z : ℂ => ‖z‖) continuous_const continuous_norm)
  have h2 : IsOpen {z : ℂ | ‖z‖ < R} := by
    simpa using
      (isOpen_lt (f := fun z : ℂ => ‖z‖) (g := fun _ : ℂ => R) continuous_norm continuous_const)
  rw [show {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} = {z : ℂ | r < ‖z‖} ∩ {z : ℂ | ‖z‖ < R} by
    ext z
    simp]
  exact h1.inter h2

private lemma annulus_mem_closure {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    (r : ℂ) ∈ closure {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  let t := min (ε / 2) ((R - r) / 2)
  have ht0 : 0 < t := lt_min (half_pos hε) (half_pos (sub_pos.mpr hrR))
  have htR : t < R - r := by
    dsimp [t]
    exact lt_of_le_of_lt (min_le_right (ε / 2) ((R - r) / 2)) (half_lt_self (sub_pos.mpr hrR))
  have htε : t < ε := by
    dsimp [t]
    exact lt_of_le_of_lt (min_le_left (ε / 2) ((R - r) / 2)) (half_lt_self hε)
  have hnorm : ‖((r : ℂ) + (t : ℂ))‖ = r + t := by
    rw [← Complex.ofReal_add]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (add_pos hr ht0)]
  have hsub : (r : ℂ) - ((r : ℂ) + (t : ℂ)) = -(t : ℂ) := by ring
  refine ⟨((r : ℂ) + (t : ℂ)), ?_, ?_⟩
  · constructor
    · rw [hnorm]
      exact lt_add_of_pos_right r ht0
    · rw [hnorm]
      linarith
  · rw [dist_eq_norm, hsub]
    rw [norm_neg, norm_ofReal_of_nonneg (le_of_lt ht0)]
    exact htε


/-- **Maximum principle for harmonic functions on a closed annulus.**  If
`u : ℂ → ℝ` is harmonic on the open annulus `{z | r < ‖z‖ ∧ ‖z‖ < R}` and
continuous on the closed annulus, and `u ≤ M` on both boundary circles,
then `u ≤ M` throughout the closed annulus.  (Compactness of the closed
annulus + the strong maximum principle for harmonic functions on the open
annulus: a maximiser in the interior forces constancy on the connected open
annulus, contradicting the boundary bound by continuity at an inner-circle
point; note the open annulus `{r < ‖z‖ < R}` is connected for `0 < r < R`.) -/
theorem annulus_le_boundary {u : ℂ → ℝ} {r R M : ℝ} (hr : 0 < r) (hrR : r < R)
    (hu : HarmonicOnNhd u {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R})
    (hc : ContinuousOn u {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R})
    (hM : ∀ z : ℂ, (‖z‖ = r ∨ ‖z‖ = R) → u z ≤ M) :
    ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ R → u z ≤ M := by
  classical
  let C : Set ℂ := {z : ℂ | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}
  have hCclosed : IsClosed C := by
    have hCeq : C = (fun z : ℂ => ‖z‖) ⁻¹' Set.Icc r R := by
      ext z
      simp [C]
    rw [hCeq]
    exact IsClosed.preimage continuous_norm isClosed_Icc
  have hCsubset : C ⊆ closedBall (0 : ℂ) R := by
    intro z hz
    rcases hz with ⟨_, hzR⟩
    simp [dist_eq_norm]
    exact hzR
  have hCcompact : IsCompact C :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) R) hCclosed hCsubset
  have hCne : C.Nonempty := by
    refine ⟨(r : ℂ), ?_⟩
    change r ≤ ‖(r : ℂ)‖ ∧ ‖(r : ℂ)‖ ≤ R
    rw [norm_ofReal_of_nonneg (le_of_lt hr)]
    exact ⟨le_rfl, le_of_lt hrR⟩
  obtain ⟨p, hpC, hpMax⟩ := hCcompact.exists_isMaxOn hCne hc
  have hp_le_M : u p ≤ M := by
    by_cases hp_int : r < ‖p‖ ∧ ‖p‖ < R
    · let A : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R}
      have hAopen : IsOpen A := by
        simpa [A] using (isOpen_annulus (r := r) (R := R))
      have hApre : IsPreconnected A := by
        simpa [A] using (preconnected_annulus hr hrR)
      have hmA : IsMaxOn u A p := by
        intro z hz
        exact hpMax ⟨le_of_lt hz.1, le_of_lt hz.2⟩
      have hconst : ∀ z ∈ A, u z = u p :=
        harmonic_eqOn_of_isMaxOn (A := A) hAopen hApre hu hp_int hmA
      have hAC : A ⊆ C := by
        intro z hz
        exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
      have hclC : closure A ⊆ C := (IsClosed.closure_subset_iff hCclosed).mpr hAC
      have hcontCl : ContinuousOn u (closure A) := hc.mono hclC
      have hEqCl : EqOn u ((fun _ : ℂ => u p)) (closure A) :=
        (show EqOn u ((fun _ : ℂ => u p)) A from hconst).of_subset_closure hcontCl
          continuousOn_const subset_closure Subset.rfl
      have hz0cl : (r : ℂ) ∈ closure A := by
        simpa [A] using (annulus_mem_closure hr hrR)
      have huz0 : u (r : ℂ) = u p := hEqCl hz0cl
      have hz0norm : ‖(r : ℂ)‖ = r := norm_ofReal_of_nonneg (le_of_lt hr)
      have huz0M : u (r : ℂ) ≤ M := hM (r : ℂ) (Or.inl hz0norm)
      rw [← huz0]
      exact huz0M
    · have hb : ‖p‖ = r ∨ ‖p‖ = R := by
        rcases hpC with ⟨hp1, hp2⟩
        rcases lt_or_ge r ‖p‖ with hrlt | hle
        · right
          exact le_antisymm hp2 (not_lt.mp (fun hRlt => hp_int ⟨hrlt, hRlt⟩))
        · left
          exact le_antisymm hle hp1
      exact hM p hb
  intro z hz1 hz2
  exact le_trans (hpMax ⟨hz1, hz2⟩) hp_le_M


end Harmonic

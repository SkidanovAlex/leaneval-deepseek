import Mathlib
import Submission.Work.Drive.N2.windowDatum
import Submission.Work.Drive.N2.footMapDefs
import Submission.Work.Drive.N2.saddleScaled

/-!
# The chart-entry invariant at the foot of a band point outside the chart

`Work.Drive.N2.im_sq_foot_ge_of_mem_C`: if `y` is a band point *outside* the Morse chart of index
`i`, and the transport of `y` to the anchor level `a = f p - λ η` lands *inside* the closed chart
region `C i`, then the invariant `Im (Z ·)²` of the sub-trajectory running inside `C i` transfers
the *chart norm* of the last point of that sub-trajectory (which lies on the boundary of `C i`,
hence has chart norm `≥ ρ i`) to the foot:

    (ρ i)² / 2  ≤  |Im ((Z (foot y))²)| .

The proof is a first-exit argument along the trajectory:

* with `T := a - f y < 0`, consider the set `S = {t | T ≤ t, Φ (t,y) ∉ C i}` of *exit times*; it is
  nonempty (`0 ∈ S`, because `Φ (0,y) = y ∉ (φ i).source ⊇ C i`) and bounded below by `T`, so
  `t₂ := sInf S` is well defined and `T ≤ t₂`;
* `t₂ ∈ C i`: otherwise `Φ (·,y)` stays outside `C i` on a whole interval below `t₂` (the complement
  of the closed `C i` is open), contradicting the infimum property (this is where `T ∈ C i` — the
  foot — is used, to keep the interval above `T`);
* `t₂ ∈ closure ((C i)ᶜ)`: `S` accumulates at `t₂` from above (infimum property) and the trajectory
  is continuous; hence `Φ (t₂,y) ∈ frontier (C i)`;
* a point of the frontier is not in the interior, while
  `{z ∈ (φ i).source | ‖φ i z‖ < ρ i} ⊆ interior (C i)` is an open subset of the closed region, so
  `‖φ i (Φ (t₂,y))‖ ≥ ρ i`;
* on `[T, t₂]` the trajectory stays in `C i`, so the level law holds there and, by `hband`,
  `|Re ((Z (Φ (t₂,y)))²)| ≤ lam`; with `Re² + Im² = ‖Z‖⁴` and `lam ≤ (ρ i)²/2` this gives
  `(ρ i)²/2 ≤ |Im ((Z (Φ (t₂,y)))²)|`;
* the invariant `him` (applied backwards from `t₂` to `T`) identifies that `Im` with
  `Im ((Z (foot y))²)`.

The hypothesis `him` is exactly the `C i`-invariant produced by the model-adapted flow
(`Work.Drive.N2.im_sq_eq_of_flow_closedODE`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

/-- The complex coordinate `z₀ + i z₁` of a point of the plane has the norm of the point. -/
lemma norm_complexOf_plane (v : EuclideanSpace ℝ (Fin 2)) :
    ‖((v 0 : ℂ) + (v 1 : ℂ) * Complex.I)‖ = ‖v‖ := by
  have h1 : ‖((v 0 : ℂ) + (v 1 : ℂ) * Complex.I)‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, sub_zero, Complex.add_im, Complex.mul_im, Complex.I_im,
      mul_one, add_zero]
    ring
  have h2 : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  have h : (‖((v 0 : ℂ) + (v 1 : ℂ) * Complex.I)‖) ^ 2 = (‖v‖) ^ 2 := by rw [h1, h2]
  have habs := (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  simpa only [abs_of_nonneg (norm_nonneg _)] using habs

/-- The Pythagorean identity for the square: `Re (z²)² + Im (z²)² = ‖z‖⁴`. -/
lemma re_sq_add_im_sq_sq (z : ℂ) : (z ^ 2).re ^ 2 + (z ^ 2).im ^ 2 = ‖z‖ ^ 4 := by
  have h1 : ‖z ^ 2‖ ^ 2 = (z ^ 2).re ^ 2 + (z ^ 2).im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have h2 : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  rw [h2] at h1
  rw [← h1]
  ring

theorem im_sq_foot_ge_of_mem_C {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p) (i : Fin D.N)
    {Zs : M → ℂ}
    (hZs : ∀ y : M, Zs y = (((D.φ i y) 0 : ℝ) : ℂ) + (((D.φ i y) 1 : ℝ) : ℂ) * Complex.I)
    (him : ∀ (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), D.Φ (u, y) ∈ D.C i) →
      ((Zs (D.Φ (t, y))) ^ 2).im = ((Zs y) ^ 2).im)
    (hlews : ∀ y ∈ (D.φ i).source, f y = f (D.x i) + ((Zs y) ^ 2).re)
    {a lam : ℝ} {y : M}
    (hysrc : y ∉ (D.φ i).source)
    (hyT : a < f y)
    (hfootC : Work.Drive.N2.footMap D.Φ f a y ∈ D.C i)
    (hband : ∀ u ∈ Set.Icc (a - f y) 0, |f (D.Φ (u, y)) - f (D.x i)| ≤ lam)
    (hlam : lam ≤ (D.ρ i) ^ 2 / 2) :
    ((D.ρ i) ^ 2) / 2 ≤ |((Zs (Work.Drive.N2.footMap D.Φ f a y)) ^ 2).im| := by
  classical
  have hΦycont : Continuous fun t : ℝ => D.Φ (t, y) :=
    D.hΦsm.continuous.comp (continuous_id.prodMk continuous_const)
  -- ## Step 0: the departure time `T = a - f y` and the foot
  set T : ℝ := a - f y with hTdef
  have hTneg : T < 0 := by rw [hTdef]; linarith
  have hfootEq : Work.Drive.N2.footMap D.Φ f a y = D.Φ (T, y) := by
    rw [footMap, ← hTdef]
  have hfootC' : D.Φ (T, y) ∈ D.C i := by rw [← hfootEq]; exact hfootC
  have hyC : y ∉ D.C i := fun h => hysrc (D.hCsub i h)
  -- ## Step 1: the set of exit times and its infimum
  set S : Set ℝ := {t : ℝ | T ≤ t ∧ D.Φ (t, y) ∉ D.C i} with hSdef
  have h0S : (0 : ℝ) ∈ S := ⟨hTneg.le, by rw [D.hΦ0]; exact hyC⟩
  have hSne : S.Nonempty := ⟨0, h0S⟩
  have hSbd : BddBelow S := ⟨T, fun t ht => ht.1⟩
  set t₂ : ℝ := sInf S with ht₂def
  have ht₂le0 : t₂ ≤ 0 := by
    rw [ht₂def]
    exact csInf_le hSbd h0S
  have ht₂T : T ≤ t₂ := by
    rw [ht₂def]
    exact le_csInf hSne (fun b hb => hb.1)
  -- `S` accumulates at `t₂` from above
  have ht₂clS : t₂ ∈ closure S := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hex : ∃ s ∈ S, s < t₂ + ε := by
      by_contra hcon
      push Not at hcon
      have hle : t₂ + ε ≤ t₂ := by
        rw [ht₂def]
        exact le_csInf hSne hcon
      linarith
    obtain ⟨s, hsS, hslt⟩ := hex
    refine ⟨s, hsS, ?_⟩
    have hge : t₂ ≤ s := by rw [ht₂def]; exact csInf_le hSbd hsS
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hclc : D.Φ (t₂, y) ∈ closure ((D.C i)ᶜ) := by
    have himg : D.Φ (t₂, y) ∈ closure ((fun t : ℝ => D.Φ (t, y)) '' S) :=
      image_closure_subset_closure_image hΦycont ⟨t₂, ht₂clS, rfl⟩
    have hsub : ((fun t : ℝ => D.Φ (t, y)) '' S) ⊆ (D.C i)ᶜ := by
      rintro z ⟨s, hs, rfl⟩
      exact hs.2
    exact closure_mono hsub himg
  -- ## Step 2: `t₂` is an entry time
  have ht₂C : D.Φ (t₂, y) ∈ D.C i := by
    rcases eq_or_lt_of_le ht₂T with h | h
    · rw [← h]; exact hfootC'
    · by_contra hnot
      have hnb : ((fun t : ℝ => D.Φ (t, y)) ⁻¹' (D.C i)ᶜ) ∈ 𝓝 t₂ :=
        hΦycont.continuousAt.preimage_mem_nhds ((D.hCclosed i).isOpen_compl.mem_nhds hnot)
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hnb
      set ε' : ℝ := min ε ((t₂ - T) / 2) with hε'def
      have hε'pos : 0 < ε' := lt_min hε (by linarith)
      have hε'le : ε' ≤ ε := min_le_left _ _
      set t : ℝ := t₂ - ε' / 2 with htdef
      have htlt : t < t₂ := by rw [htdef]; linarith
      have htT : T ≤ t := by
        have h2 : ε' ≤ (t₂ - T) / 2 := min_le_right _ _
        rw [htdef]; linarith
      have hball : t ∈ Metric.ball t₂ ε := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> · rw [htdef]; linarith
      have htS : t ∈ S := ⟨htT, hεsub hball⟩
      have : t₂ ≤ t := by rw [ht₂def]; exact csInf_le hSbd htS
      linarith
  -- every time of `[T, t₂]` is an entry time
  have ht₂Icc : ∀ u ∈ Set.Icc T t₂, D.Φ (u, y) ∈ D.C i := by
    intro u hu
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]; exact ht₂C
    · by_contra hnot
      have huS : u ∈ S := ⟨hu.1, hnot⟩
      have : t₂ ≤ u := by rw [ht₂def]; exact csInf_le hSbd huS
      linarith
  -- ## Step 3: the frontier and the chart norm
  have hfront : D.Φ (t₂, y) ∈ frontier (D.C i) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure ht₂C, hclc⟩
  have hnorm : D.ρ i ≤ ‖D.φ i (D.Φ (t₂, y))‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hsrcC : D.Φ (t₂, y) ∈ (D.φ i).source := D.hCsub i ht₂C
    have hopen : IsOpen ((D.φ i).source ∩ (D.φ i) ⁻¹' Metric.ball 0 (D.ρ i)) :=
      ContinuousOn.isOpen_inter_preimage (D.hφ i).continuousOn (D.φ i).open_source
        Metric.isOpen_ball
    have hsub : ((D.φ i).source ∩ (D.φ i) ⁻¹' Metric.ball 0 (D.ρ i)) ⊆ D.C i := by
      rintro z ⟨hzsrc, hzball⟩
      exact D.hCop i ⟨hzsrc, by simpa [Metric.mem_ball] using hzball⟩
    have hint : D.Φ (t₂, y) ∈ interior (D.C i) :=
      interior_maximal hsub hopen ⟨hsrcC, by simpa [Metric.mem_ball] using hlt⟩
    have hfr := hfront
    rw [frontier_eq_closure_inter_closure, closure_compl] at hfr
    exact hfr.2 hint
  have hZsnorm : ‖Zs (D.Φ (t₂, y))‖ = ‖D.φ i (D.Φ (t₂, y))‖ := by
    rw [hZs]
    exact norm_complexOf_plane _
  -- ## Step 4: the level law on the sub-trajectory
  have hre : |((Zs (D.Φ (t₂, y))) ^ 2).re| ≤ lam := by
    have hb := hband t₂ ⟨ht₂T, ht₂le0⟩
    have h := hlews _ (D.hCsub i ht₂C)
    have h2 : f (D.Φ (t₂, y)) - f (D.x i) = ((Zs (D.Φ (t₂, y))) ^ 2).re := by linarith
    rw [← h2]
    exact hb
  -- ## Step 5: the invariant transfers the bound to the foot
  have him2 : ((Zs (D.Φ (T, y))) ^ 2).im = ((Zs (D.Φ (t₂, y))) ^ 2).im := by
    have hlt : T - t₂ ≤ 0 := by linarith
    have hconf : ∀ u ∈ Set.Icc (min 0 (T - t₂)) (max 0 (T - t₂)),
        D.Φ (u, D.Φ (t₂, y)) ∈ D.C i := by
      intro u hu
      rw [min_eq_right hlt, max_eq_left hlt] at hu
      rw [D.hΦcomp]
      exact ht₂Icc (u + t₂) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h := him (D.Φ (t₂, y)) (T - t₂) hconf
    have h2 : D.Φ (T - t₂, D.Φ (t₂, y)) = D.Φ (T, y) := by
      rw [D.hΦcomp]; ring_nf
    rw [h2] at h
    exact h
  rw [hfootEq, him2]
  -- ## Step 6: the arithmetic
  have hρpos : 0 < D.ρ i := D.hρ i
  have hlam0 : 0 ≤ lam := le_trans (abs_nonneg _) (hband T ⟨le_rfl, hTneg.le⟩)
  have hmain : ((D.ρ i) ^ 2 / 2) ^ 2 ≤ ((Zs (D.Φ (t₂, y))) ^ 2).im ^ 2 := by
    have h1 : (D.ρ i) ^ 4 ≤ ((Zs (D.Φ (t₂, y))) ^ 2).re ^ 2
        + ((Zs (D.Φ (t₂, y))) ^ 2).im ^ 2 := by
      rw [re_sq_add_im_sq_sq, hZsnorm]
      exact pow_le_pow_left₀ hρpos.le hnorm 4
    have h2 : ((Zs (D.Φ (t₂, y))) ^ 2).re ^ 2 ≤ lam ^ 2 := by
      have hab := abs_le.mp hre
      nlinarith [hab.1, hab.2]
    nlinarith [h1, h2, hlam, hlam0, hρpos]
  have hfin : (D.ρ i) ^ 2 / 2 ≤ |((Zs (D.Φ (t₂, y))) ^ 2).im| := by
    have h := (sq_le_sq).mp hmain
    rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (D.ρ i) ^ 2 / 2)] at h
  exact hfin

end Work.Drive.N2

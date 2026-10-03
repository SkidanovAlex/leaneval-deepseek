import Mathlib
import Submission.Work.L61.Basic
import Submission.Work.Parab.germ
import Submission.Work.FatouCoord.Repelling

/-!
# Lemma 6.1 (Shishikura §6), repelling-orbit part

The pushed-down horn map `g = pushdown Ẽ_{f₀}` of a parabolic germ in `𝓕₀` has `0` as a
parabolic fixed point.  Hence there is a **repelling inverse orbit** of `g`: a sequence
`wd` with `g (wd (j+1)) = wd j` for all `j`, converging to `0`, which never hits `0` nor
any point of the critical orbit of `g` (`Kset`), and whose points (from `wd 1` on) lie in
the domain `gdom` of `g`.

This is the "Since `0` is a parabolic fixed point of `g₀`, there exists an inverse orbit
`{w''_j}` ..." step in the proof of Lemma 6.1.  The orbit is produced from the repelling
petal of the rescaled horn map `ǧ = gres d ∈ 𝓕₀` (`HornData.g_F0`), and the avoidance of
the (countable) critical orbit is by a genericity argument over the uncountably many
repelling orbits in the petal.
-/

namespace Work.L61.Repel

open MandelDim Set Function Metric Filter
open scoped Topology
open Work.FatouCoord

noncomputable section

variable {f₀ : ℂ → ℂ} {D₀ : Set ℂ}

/-! ## Elementary algebraic facts about the rescaled horn map -/

theorem gres_eq (d : ParabData f₀ D₀) (ζ : ℂ) :
    gres d ζ = (deriv (deriv (g d)) 0 / 2) * g d (ζ / (deriv (deriv (g d)) 0 / 2)) := rfl

theorem gres_smul {d : ParabData f₀ D₀} (hs : deriv (deriv (g d)) 0 / 2 ≠ 0) (ζ : ℂ) :
    gres d ((deriv (deriv (g d)) 0 / 2) * ζ) = (deriv (deriv (g d)) 0 / 2) * g d ζ := by
  rw [gres_eq, show (deriv (deriv (g d)) 0 / 2) * ζ / (deriv (deriv (g d)) 0 / 2) = ζ from
    mul_div_cancel_left₀ ζ hs]

theorem gres_iter {d : ParabData f₀ D₀} (hs : deriv (deriv (g d)) 0 / 2 ≠ 0) (n : ℕ)
    (ζ : ℂ) : (gres d)^[n] ((deriv (deriv (g d)) 0 / 2) * ζ) =
      (deriv (deriv (g d)) 0 / 2) * (g d)^[n] ζ := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, gres_smul hs, Function.iterate_succ_apply']

/-- The `Kset` of `g` in the `gres`-coordinates: `ζ / s` lies on the critical orbit of `g`
iff `ζ` lies on the (scaled) critical orbit of `gres`. -/
theorem mem_Kset_iff_rescale {d : ParabData f₀ D₀} (hd : HornData d) (ζ : ℂ) :
    ζ / (deriv (deriv (g d)) 0 / 2) ∈ Kset d hd ↔
      ζ ∈ ({0} : Set ℂ) ∪ Set.range
        (fun n : ℕ => (gres d)^[n] ((deriv (deriv (g d)) 0 / 2) * critVal hd)) := by
  have hs : deriv (deriv (g d)) 0 / 2 ≠ 0 := by
    refine div_ne_zero ?_ (by norm_num)
    simpa [g] using hd.g_second
  simp only [Kset, Set.mem_union, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (h | ⟨n, hn⟩)
    · left; exact (div_eq_zero_iff.mp h).resolve_right hs
    · right
      refine ⟨n, ?_⟩
      rw [gres_iter hs n (critVal hd), hn, mul_div_cancel₀ ζ hs]
  · rintro (h | ⟨n, hn⟩)
    · left; rw [h, zero_div]
    · right
      refine ⟨n, (eq_div_iff hs).mpr ?_⟩
      rw [mul_comm, ← gres_iter hs n (critVal hd), hn]

/-! ## The punctured disc around `0` is contained in `gdom` -/

/-- `π` maps the half-plane `{Im > η}` onto the punctured disc of radius `e^{-2πη}`; since
that half-plane lies in `Bu`, the punctured disc lies in `gdom = {0} ∪ π(Bu ∪ Bl)`. -/
theorem punctured_subset_gdom (d : ParabData f₀ D₀) (hd : HornData d) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hζ' : ‖ζ‖ < Real.exp (-(2 * Real.pi * hd.η))) : ζ ∈ gdom d hd := by
  set w₀ : ℂ := Complex.log ζ / (2 * Real.pi * Complex.I) with hw₀
  have hπ : piExp w₀ = ζ := piExp_log_div ζ hζ
  have hre : (2 * (Real.pi : ℂ) * Complex.I * w₀).re = -(2 * Real.pi * w₀.im) := by
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hnorm : ‖ζ‖ = Real.exp (-(2 * Real.pi * w₀.im)) := by
    rw [← hπ, piExp, Complex.norm_exp, hre]
  have him : hd.η < w₀.im := by
    rw [hnorm] at hζ'
    have := Real.exp_lt_exp.mp hζ'
    nlinarith [Real.pi_pos]
  exact mem_insert_of_mem _ ⟨w₀, Or.inl (hd.upper him), hπ⟩

/-! ## Genericity: a repelling orbit avoiding a countable set -/

theorem not_countable_Ioo {a b : ℝ} (h : a < b) : ¬ (Set.Ioo a b).Countable := by
  intro hc
  rw [← Cardinal.le_aleph0_iff_set_countable] at hc
  rw [Cardinal.mk_Ioo_real h] at hc
  exact absurd hc (not_le.mpr Cardinal.aleph0_lt_continuum)

/-- In an open set `P ∋ p` (here a repelling petal, so that `finv` is injective on `P`)
there is a `finv`-orbit avoiding a countable set.  The bad set of starting points is a
countable union of countable sets, while any neighbourhood of `p` is uncountable. -/
theorem exists_orbit_avoiding_countable {f finv : ℂ → ℂ} {P : Set ℂ}
    (hpet : IsRepellingPetal f finv P) {K' : Set ℂ} (hK : K'.Countable)
    {p : ℂ} (hp : p ∈ P) : ∃ u ∈ P, ∀ m : ℕ, finv^[m] u ∉ K' := by
  obtain ⟨hPopen, hP0, hmaps, hfinv, _⟩ := hpet
  have hinj : InjOn finv P := by
    intro a ha b hb hab
    calc a = f (finv a) := (hfinv a ha).symm
      _ = f (finv b) := by rw [hab]
      _ = b := hfinv b hb
  have hinj_iter : ∀ m : ℕ, InjOn (finv^[m]) P := by
    intro m
    induction m with
    | zero => intro a _ b _ h; simpa using h
    | succ k ih =>
      intro a ha b hb hab
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply] at hab
      exact hinj ha hb (ih (hmaps ha) (hmaps hb) hab)
  set Bad : Set ℂ := {u | u ∈ P ∧ ∃ m : ℕ, finv^[m] u ∈ K'} with hBaddef
  have hBad_count : Bad.Countable := by
    have heq : Bad = ⋃ m : ℕ, ((finv^[m]) ⁻¹' K') ∩ P := by
      rw [hBaddef]
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [heq]
    refine Set.countable_iUnion (fun m => ?_)
    refine Set.MapsTo.countable_of_injOn (f := fun x : ℂ => finv^[m] x) ?_ ?_ hK
    · intro x hx
      exact hx.1
    · intro a ha b hb hab
      exact hinj_iter m ha.2 hb.2 hab
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hPopen p hp
  have hIoo_unc : ¬ (Set.Ioo (-ρ) ρ).Countable := not_countable_Ioo (by linarith)
  by_contra hcon
  push_neg at hcon
  have hsub : Set.Ioo (-ρ) ρ ⊆ {t : ℝ | p + (t : ℂ) ∈ Bad} := by
    intro t ht
    have hmem : p + (t : ℂ) ∈ Metric.ball p ρ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : p + (t : ℂ) - p = (t : ℂ) := by ring
      rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_lt]
      exact ht
    exact ⟨hρsub hmem, hcon _ (hρsub hmem)⟩
  have hcount2 : ({t : ℝ | p + (t : ℂ) ∈ Bad}).Countable := by
    refine hBad_count.preimage ?_
    intro a b hab
    exact Complex.ofReal_injective (add_left_cancel hab)
  exact hIoo_unc (hcount2.mono hsub)

/-! ## The repelling orbit -/

theorem exists_repelling_orbit {f₀ : ℂ → ℂ} {D₀ : Set ℂ} {d : MandelDim.ParabData f₀ D₀}
    (hd : MandelDim.HornData d) :
    ∃ wd : ℕ → ℂ, (∀ j, wd j ≠ 0) ∧ (∀ j, wd j ∉ Work.L61.Kset d hd) ∧
      (∀ j, wd (j + 1) ∈ Work.L61.gdom d hd) ∧ (∀ j, Work.L61.g d (wd (j + 1)) = wd j) ∧
      Filter.Tendsto wd Filter.atTop (nhds 0) := by
  have hs : deriv (deriv (g d)) 0 / 2 ≠ 0 := by
    refine div_ne_zero ?_ (by norm_num)
    simpa [g] using hd.g_second
  -- the rescaled horn map lies in 𝓕₀, so it carries a repelling petal
  have hgerm : IsParabolicGerm (gres d)
      ((fun ζ : ℂ => deriv (deriv (g d)) 0 / 2 * ζ) '' insert 0 (piExp '' (hd.Bu ∪ hd.Bl))) :=
    hd.g_F0.1
  obtain ⟨h, a, r, A, A', hb, _⟩ := Work.Parab.exists_parabolicBounds_of_germ hgerm
  obtain ⟨finv, r', M, ψ, hr', hM, hpet, _⟩ := Work.FatouCoord.exists_repelling_petal hb
  -- the (scaled) critical orbit of `gres`
  set K' : Set ℂ := ({0} : Set ℂ) ∪ Set.range
    (fun n : ℕ => (gres d)^[n] ((deriv (deriv (g d)) 0 / 2) * critVal hd)) with hK'def
  have hK'c : K'.Countable := by
    rw [hK'def]
    exact (Set.countable_singleton 0).union (Set.countable_range _)
  -- the repelling petal is nonempty
  have hmpos : 0 < min r' M⁻¹ := lt_min hr' (by positivity)
  have hmemP : ((min r' M⁻¹ / 2 : ℝ) : ℂ) ∈ PetalRep r' M := by
    rw [mem_PetalRep]
    constructor
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      have := min_le_left r' M⁻¹
      linarith
    · rw [Complex.normSq_ofReal, Complex.ofReal_re]
      have h1 : min r' M⁻¹ ≤ M⁻¹ := min_le_right _ _
      have h2 : M * min r' M⁻¹ ≤ 1 := by
        have := mul_le_mul_of_nonneg_left h1 (le_of_lt hM)
        rwa [mul_inv_cancel₀ (ne_of_gt hM)] at this
      nlinarith [hmpos]
  obtain ⟨u, huP, huBad⟩ := exists_orbit_avoiding_countable hpet hK'c hmemP
  have htend : Tendsto (fun m : ℕ => finv^[m] u) atTop (nhds 0) := hpet.2.2.2.2 u huP
  -- the orbit is eventually inside the punctured disc contained in `gdom`
  have hRpos : 0 < Real.exp (-(2 * Real.pi * hd.η)) * ‖deriv (deriv (g d)) 0 / 2‖ :=
    mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hs)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ m : ℕ, J ≤ m →
      ‖finv^[m] u‖ < Real.exp (-(2 * Real.pi * hd.η)) * ‖deriv (deriv (g d)) 0 / 2‖ := by
    rcases Filter.eventually_atTop.mp (htend.eventually (Metric.ball_mem_nhds (0 : ℂ) hRpos)) with
      ⟨J, hJ⟩
    exact ⟨J, fun m hm => by
      have := hJ m hm
      rwa [dist_zero_right] at this⟩
  refine ⟨fun j : ℕ => finv^[j + J] u / (deriv (deriv (g d)) 0 / 2), ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have hP : finv^[j + J] u ∈ PetalRep r' M :=
      mapsTo_iterate_of_mapsTo hpet.2.2.1 (j + J) huP
    exact div_ne_zero (hpet.2.1 hP) hs
  · intro j hc
    exact huBad (j + J) ((mem_Kset_iff_rescale hd _).mp hc)
  · intro j
    have hP : finv^[(j + 1) + J] u ∈ PetalRep r' M :=
      mapsTo_iterate_of_mapsTo hpet.2.2.1 ((j + 1) + J) huP
    have hne : finv^[(j + 1) + J] u ≠ 0 := hpet.2.1 hP
    have hsm : ‖finv^[(j + 1) + J] u‖ <
        Real.exp (-(2 * Real.pi * hd.η)) * ‖deriv (deriv (g d)) 0 / 2‖ := hJ _ (by omega)
    have hlt : ‖finv^[(j + 1) + J] u / (deriv (deriv (g d)) 0 / 2)‖ <
        Real.exp (-(2 * Real.pi * hd.η)) := by
      rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hs)]
      exact hsm
    exact punctured_subset_gdom d hd (div_ne_zero hne hs) hlt
  · intro j
    dsimp only
    have hP : finv^[j + J] u ∈ PetalRep r' M :=
      mapsTo_iterate_of_mapsTo hpet.2.2.1 (j + J) huP
    have hiter : finv^[(j + 1) + J] u = finv (finv^[j + J] u) := by
      rw [show (j + 1) + J = (j + J) + 1 by omega, Function.iterate_succ_apply']
    have hgr : gres d (finv (finv^[j + J] u)) = finv^[j + J] u := hpet.2.2.2.1 _ hP
    rw [hiter]
    rw [gres_eq] at hgr
    have hcancel : deriv (deriv (g d)) 0 / 2 * (finv^[j + J] u / (deriv (deriv (g d)) 0 / 2))
        = finv^[j + J] u := mul_div_cancel₀ _ hs
    apply mul_left_cancel₀ hs
    rw [hgr, hcancel]
  · have h1 : Tendsto (fun j : ℕ => finv^[j + J] u) atTop (nhds 0) :=
      htend.comp (Filter.tendsto_add_atTop_nat J)
    simpa using h1.div_const (deriv (deriv (g d)) 0 / 2)

end

end Work.L61.Repel

import Mathlib
import Submission.Work.EKLC6Core.ae_uncrossed_cellbase
import Submission.Work.EKLC6Core.desc_plaque_algebra_conull_ergodic_gen
import Submission.Work.EKLC6Core.ae_ball_in_atom
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLC6Core.measure_iInter_iUnion_exp_eq_zero

/-!
# `Work.EKLC6Core.past_atom_contains_Uball_of_thin_frontier`

For an `aDiag t`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and a countable family
`Q : ℕ → Set X₃` of open sets whose *union of frontiers* is `μ`-thin in the linear sense

`μ (⋃ k, VThick η (frontier (Q k))) ≤ d · η`   (`d > 0`),

for `μ`-a.e. `x` there is `δ > 0` such that every `u ∈ Uball (Uminus t) δ` preserves the *whole
past itinerary* of `x`: for every `n` and `k`,

`aDiag(t)^n · x ∈ Q k  →  aDiag(t)^n · (u · x) ∈ Q k`.

Equivalently, the past atom of `x` (the set of points with the same itinerary with respect to
the family `Q`) contains the `Uminus t`-ball of radius `δ` around `x`.

## Proof

This is the tracking (Borel–Cantelli) argument of `Work.EKLC6Core.ae_ball_in_atom`, for the
linear thinness bound and for a countable (rather than finite) family of cells.

* `NbdQ Q η = ⋃ k, VThick η (frontier (Q k))` is the set whose mass is bounded by `d η`, and
  `CrossesQ Q τ y` says that some `v ∈ V τ` moves `y` from a member of `Q` out of it.
* `crossing_memQ`: if `y` is crossed at a small scale `τ ≤ 1/800`, then `y ∈ NbdQ Q (500 τ)`
  (the crossing point of a path from `1` to `v` inside `V (100 τ)` lies on the frontier, and its
  inverse is in `V (500 τ)`).
* Hence for every `η` the set of points *not* crossed at some positive scale is small:
  the set `G` of points uncrossed at scale `1/(k+801)` (some `k`) satisfies `μ Gᶜ = 0`
  (`hGnull`), using `⋃ k {uncrossed at 1/(k+801)}` and the linear bound.
* By the geometric Borel–Cantelli lemma applied to the orbit of the measurable hulls of
  `NbdQ Q (500 e^{-αn})` (with `α > 0` the contraction rate of `Uminus t`), `μ`-a.e. `x` avoids
  those scales for all large `n`; combined with `G` this gives, for the finitely many early
  times, a positive scale at which no crossing happens, and one takes the (finite) minimum over
  these corrected by `e^{αn}` to obtain the required `δ`.
* The contraction `aDiag(t)^n · u · (aDiag(t)^n)⁻¹ ∈ V (e^{-αn} δ)` (from
  `contraction_rate_uminus`) then shows that no `u ∈ V δ` can move the `n`-th orbit point out of
  its cell, i.e. the itineraries of `x` and `u · x` agree.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The countable thin-boundary neighbourhood: the union over `k` of the `η`-thickenings of the
frontiers of the family `Q`.  This is the set whose mass the thin-boundary hypothesis bounds. -/
def NbdQ (Q : ℕ → Set X3) (η : ℝ) : Set X3 :=
  ⋃ k, VThick η (frontier (Q k))

/-- `CrossesQ Q τ y` says that some `v ∈ V τ` moves `y` from a member of `Q` into a different
one. -/
def CrossesQ (Q : ℕ → Set X3) (τ : ℝ) (y : X3) : Prop :=
  ∃ k : ℕ, ∃ v : SL3, v ∈ V τ ∧ ((y ∈ Q k ∧ v • y ∉ Q k) ∨ (y ∉ Q k ∧ v • y ∈ Q k))

theorem mem_NbdQ_iff {Q : ℕ → Set X3} {η : ℝ} {y : X3} :
    y ∈ NbdQ Q η ↔ ∃ k : ℕ, ∃ g ∈ V η, ∃ z ∈ frontier (Q k), g • z = y := by
  simp only [NbdQ, VThick, Set.mem_iUnion, Set.mem_image, Set.mem_prod]
  constructor
  · rintro ⟨k, p, hp, rfl⟩
    exact ⟨k, p.1, hp.1, p.2, hp.2, rfl⟩
  · rintro ⟨k, g, hg, z, hz, h⟩
    exact ⟨k, (g, z), ⟨hg, hz⟩, h⟩

theorem CrossesQ_mono {Q : ℕ → Set X3} {τ τ' : ℝ} (hle : τ ≤ τ') {y : X3}
    (h : CrossesQ Q τ y) : CrossesQ Q τ' y := by
  obtain ⟨k, v, hv, hcase⟩ := h
  exact ⟨k, v, V_mono hle hv, hcase⟩

/-- **Pisa 7.31 (geometric core), countable family.**  If `y` is crossed at a small scale `τ`,
then `y` lies in the `(500 τ)`-neighbourhood of the boundary family. -/
theorem crossing_memQ {Q : ℕ → Set X3} {τ : ℝ} (hτ : 0 < τ) (hτle : τ ≤ 1 / 800)
    {y : X3} (hy : CrossesQ Q τ y) : y ∈ NbdQ Q (500 * τ) := by
  obtain ⟨k, v, hv, hcase⟩ := hy
  have hs : (0 : ℝ) < 100 * τ := by linarith
  have hs1 : 100 * τ ≤ 1 := by linarith
  have hs8 : 100 * τ ≤ 1 / 8 := by linarith
  have hv' : v ∈ V (100 * τ / 100) := by
    rw [show (100 : ℝ) * τ / 100 = τ by ring]
    exact hv
  obtain ⟨γ, hγcont, hγ0, hγ1, hγmem⟩ := aeBall_path hs hs1 hv'
  have hfront : ∃ θ ∈ Set.Icc (0 : ℝ) 1, γ θ • y ∈ frontier (Q k) := by
    rcases hcase with ⟨hyP, hvP⟩ | ⟨hyP, hvP⟩
    · exact exists_frontier_of_smul_path hγcont (by rw [hγ0, one_smul]; exact hyP)
        (by rw [hγ1]; exact hvP)
    · obtain ⟨θ, hθ, hθf⟩ := exists_frontier_of_smul_path (S := (Q k)ᶜ) hγcont
        (by rw [hγ0, one_smul]; exact hyP) (by rw [hγ1]; simpa using hvP)
      exact ⟨θ, hθ, by rwa [frontier_compl] at hθf⟩
  obtain ⟨θ, hθ, hθf⟩ := hfront
  have hinv : (γ θ)⁻¹ ∈ V (500 * τ) := by
    have h5 : (γ θ)⁻¹ ∈ V (5 * (100 * τ)) := aeBall_V_inv hs hs8 (hγmem θ hθ)
    rwa [show (5 : ℝ) * (100 * τ) = 500 * τ by ring] at h5
  rw [mem_NbdQ_iff]
  exact ⟨k, (γ θ)⁻¹, hinv, γ θ • y, hθf, by rw [← mul_smul, inv_mul_cancel, one_smul]⟩

theorem past_atom_contains_Uball_of_thin_frontier {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (Q : ℕ → Set Work.EKLContract.X3) (hQopen : ∀ k, IsOpen (Q k)) {d : ℝ} (hd : 0 < d)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ k, Work.EKLC6Core.VThick η (frontier (Q k))) ≤ ENNReal.ofReal (d * η)) :
    ∀ᵐ x ∂μ, ∃ δ : ℝ, 0 < δ ∧
      ∀ u ∈ Work.EKLComp.Uball (Work.EKLC6Core.Uminus t) δ, ∀ n : ℕ, ∀ k : ℕ,
      ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) x ∈ Q k →
      ((fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)^[n]) (u • x) ∈ Q k := by
  classical
  obtain ⟨α, hα, hcontr⟩ := contraction_rate_uminus t
  set a : X3 → X3 := fun y => aDiag t • y with ha
  have hamp : MeasurePreserving a μ μ := by rw [ha]; exact hmp
  have hNbd : ∀ η : ℝ, 0 < η → μ (NbdQ Q η) ≤ ENNReal.ofReal (d * η) :=
    fun η hη => hthin η hη
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.exp (-(α * (n : ℝ))) ≤ 1 / 800 := by
    have hbase0 : (0 : ℝ) ≤ Real.exp (-α) := Real.exp_nonneg _
    have hbase1 : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have htend : Tendsto (fun n : ℕ => Real.exp (-α) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
    have htend' : Tendsto (fun n : ℕ => Real.exp (-(α * (n : ℝ)))) atTop (𝓝 0) := by
      refine htend.congr' ?_
      filter_upwards with n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hev : ∀ᶠ n : ℕ in atTop, Real.exp (-(α * (n : ℝ))) < 1 / 800 :=
      htend'.eventually (isOpen_Iio.mem_nhds (by norm_num))
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hev
    exact ⟨n₁, fun n hn => le_of_lt (hn₁ n hn)⟩
  choose T hTsub hTmeas hTμ using fun n : ℕ =>
    MeasureTheory.exists_measurable_superset μ (NbdQ Q (500 * Real.exp (-(α * (n : ℝ)))))
  have hTbound : ∀ n : ℕ,
      μ (T n) ≤ ENNReal.ofReal ((d * 500) * Real.exp (-(α * (n : ℝ)))) := by
    intro n
    rw [hTμ n]
    refine le_trans (hNbd _ (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    exact le_of_eq (by ring)
  have hAbound : ∀ n : ℕ,
      μ (a^[n] ⁻¹' T n) ≤ ENNReal.ofReal ((d * 500) * Real.exp (-(α * (n : ℝ)))) := by
    intro n
    rw [(hamp.iterate n).measure_preimage (hTmeas n).nullMeasurableSet]
    exact hTbound n
  have hBC : μ (⋂ N' : ℕ, ⋃ n ≥ N', (a^[n] ⁻¹' T n)) = 0 :=
    measure_iInter_iUnion_exp_eq_zero μ (fun n => a^[n] ⁻¹' T n) (by positivity) hα hAbound
  have hBCae : ∀ᵐ x ∂μ, ∃ N₀ : ℕ, ∀ n ≥ N₀, x ∉ a^[n] ⁻¹' T n := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : X3 | ¬ ∃ N₀ : ℕ, ∀ n ≥ N₀, x ∉ a^[n] ⁻¹' T n}
        = ⋂ N' : ℕ, ⋃ n ≥ N', (a^[n] ⁻¹' T n) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
      push Not
      constructor
      · intro h N'
        obtain ⟨n, hn⟩ := h N'
        exact ⟨n, hn.1, hn.2⟩
      · intro h N'
        obtain ⟨n, hn1, hn2⟩ := h N'
        exact ⟨n, hn1, hn2⟩
    rw [hset]
    exact hBC
  set G : Set X3 := ⋃ k : ℕ, {y : X3 | ¬ CrossesQ Q (1 / ((k : ℝ) + 801)) y} with hG
  have hcross_of_not_mem : ∀ k : ℕ, ∀ y : X3, y ∉ G → CrossesQ Q (1 / ((k : ℝ) + 801)) y := by
    intro k y hy
    by_contra hcon
    refine hy ?_
    rw [hG]
    exact Set.mem_iUnion.mpr ⟨k, hcon⟩
  have hGsub : ∀ k : ℕ, Gᶜ ⊆ NbdQ Q (500 * (1 / ((k : ℝ) + 801))) := by
    intro k y hy
    refine crossing_memQ (by positivity) ?_ (hcross_of_not_mem k y hy)
    refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 800) ?_
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hGnull : μ Gᶜ = 0 := by
    refine eq_zero_of_forall_le_ofReal fun ε hε => ?_
    obtain ⟨k, hk⟩ : ∃ k : ℕ, d * (500 / ((k : ℝ) + 801)) ≤ ε := by
      obtain ⟨m, hm⟩ := exists_nat_ge (d * 500 / ε + 1)
      refine ⟨m, ?_⟩
      have h1 : d * 500 / ε + 1 ≤ (m : ℝ) := hm
      have h2 : d * 500 / ε ≤ (m : ℝ) := by linarith
      have h3 : d * 500 ≤ (m : ℝ) * ε := by
        rw [div_le_iff₀ hε] at h2; linarith
      have h4 : d * (500 / ((m : ℝ) + 801)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 801)]
        nlinarith [h3, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)),
          (show (0 : ℝ) ≤ d * 500 by positivity)]
      exact h4
    refine le_trans (measure_mono (hGsub k)) ?_
    refine le_trans (hNbd _ (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    rw [show d * (500 * (1 / ((k : ℝ) + 801))) = d * (500 / ((k : ℝ) + 801)) by ring]
    exact hk
  have hGae : ∀ᵐ x ∂μ, ∀ n : ℕ, a^[n] x ∈ G := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : X3 | ¬ ∀ n : ℕ, a^[n] x ∈ G} = ⋃ n, a^[n] ⁻¹' Gᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, not_forall, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_compl_iff]
    rw [hset]
    obtain ⟨Z, hZG, hZmeas, hZμ⟩ := MeasureTheory.exists_measurable_superset μ Gᶜ
    have hZ0 : μ Z = 0 := by rw [hZμ]; exact hGnull
    have hterm : ∀ n : ℕ, μ (a^[n] ⁻¹' Z) = 0 := fun n => by
      rw [(hamp.iterate n).measure_preimage hZmeas.nullMeasurableSet, hZ0]
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, a^[n] ⁻¹' Gᶜ)
        ≤ ∑' n : ℕ, μ (a^[n] ⁻¹' Gᶜ) := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, μ (a^[n] ⁻¹' Z) :=
          ENNReal.tsum_le_tsum fun n => measure_mono (Set.preimage_mono hZG)
      _ = 0 := by rw [show (fun n : ℕ => μ (a^[n] ⁻¹' Z)) = fun _ => 0 from funext hterm,
          tsum_zero]
  filter_upwards [hBCae, hGae] with x hxBC hxG
  obtain ⟨N₀, hN₀⟩ := hxBC
  have hxG' : ∀ n : ℕ, ∃ k : ℕ, ¬ CrossesQ Q (1 / ((k : ℝ) + 801)) (a^[n] x) := by
    intro n
    have h := hxG n
    rw [hG, Set.mem_iUnion] at h
    simpa only [Set.mem_ofPred_eq] using h
  choose kn hkn using hxG'
  have hknpos : ∀ n : ℕ, 0 < 1 / ((kn n : ℝ) + 801) := fun n => by positivity
  obtain ⟨n₁, -, hn₁min⟩ := Finset.exists_min_image (Finset.range (max N₀ n₀ + 1))
    (fun n : ℕ => (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n))
    ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
  set δ : ℝ := min 1 ((1 / ((kn n₁ : ℝ) + 801)) * Real.exp (α * n₁)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (mul_pos (hknpos n₁) (Real.exp_pos _))
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδle : ∀ n < max N₀ n₀ + 1,
      δ ≤ (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n) := by
    intro n hn
    rw [hδ]
    exact le_trans (min_le_right _ _) (hn₁min n (Finset.mem_range.mpr hn))
  refine ⟨δ, hδpos, ?_⟩
  intro u huUball n k hnk
  obtain ⟨huU, huV⟩ := huUball
  have hfine : ∀ n : ℕ, ¬ CrossesQ Q (Real.exp (-(α * (n : ℝ))) * δ) (a^[n] x) := by
    intro n
    rcases lt_or_ge n (max N₀ n₀ + 1) with hn | hn
    · have hle : δ ≤ (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n) := hδle n hn
      have hscale : Real.exp (-(α * (n : ℝ))) * δ ≤ 1 / ((kn n : ℝ) + 801) := by
        have h2 : δ * Real.exp (-(α * (n : ℝ))) ≤
            ((1 / ((kn n : ℝ) + 801)) * Real.exp (α * n)) * Real.exp (-(α * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        have h3 : Real.exp (α * n) * Real.exp (-(α * (n : ℝ))) = 1 := by
          rw [← Real.exp_add]
          ring_nf
          exact Real.exp_zero
        calc Real.exp (-(α * (n : ℝ))) * δ = δ * Real.exp (-(α * (n : ℝ))) := by ring
          _ ≤ ((1 / ((kn n : ℝ) + 801)) * Real.exp (α * n)) *
                Real.exp (-(α * (n : ℝ))) := h2
          _ = 1 / ((kn n : ℝ) + 801) := by rw [mul_assoc, h3, mul_one]
      exact fun hc' => hkn n (CrossesQ_mono hscale hc')
    · have hnm : max N₀ n₀ ≤ n := by omega
      have hN0n : N₀ ≤ n := le_trans (le_max_left _ _) hnm
      have hn0n : n₀ ≤ n := le_trans (le_max_right _ _) hnm
      have hnotT : a^[n] x ∉ T n := fun hc' => hN₀ n hN0n hc'
      have hnotN : a^[n] x ∉ NbdQ Q (500 * Real.exp (-(α * (n : ℝ)))) :=
        fun hc' => hnotT (hTsub n hc')
      have hexp : Real.exp (-(α * (n : ℝ))) ≤ 1 / 800 := hn₀ n hn0n
      have hexppos : 0 < Real.exp (-(α * (n : ℝ))) := Real.exp_pos _
      have hscale : Real.exp (-(α * (n : ℝ))) * δ ≤ Real.exp (-(α * (n : ℝ))) := by
        nlinarith [Real.exp_pos (-(α * (n : ℝ)))]
      exact fun hc' => hnotN (crossing_memQ hexppos hexp (CrossesQ_mono hscale hc'))
  have hw : aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ V (Real.exp (-(α * (n : ℝ))) * δ) :=
    hcontr n δ hδpos u huU huV
  have hnot : ¬ CrossesQ Q (Real.exp (-(α * (n : ℝ))) * δ) (a^[n] x) := hfine n
  rw [orbit_smul_eq t n u x]
  by_contra hcon
  exact hnot ⟨k, _, hw, Or.inl ⟨hnk, hcon⟩⟩

end Work.EKLC6Core

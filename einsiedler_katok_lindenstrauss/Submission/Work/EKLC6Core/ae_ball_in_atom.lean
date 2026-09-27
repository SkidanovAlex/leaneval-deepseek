import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.aeBall_V_inv
import Submission.Work.EKLC6Core.exists_mem_frontier_of_continuousOn
import Submission.Work.EKLC6Core.measure_iInter_iUnion_exp_eq_zero
import Submission.Work.EKLC6Core.aeBall_path

/-!
# `Work.EKLC6Core.ae_ball_in_atom` — Pisa Lemma 7.31 (tracking)

For an `A`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, an exponent vector `t`, a finite
family `P : Fin N → Set X₃` whose boundary is `μ`-thin (the `η`-neighbourhood of the union of
the frontiers has mass `≤ c η`), and a contracting estimate for `Uminus t` along `aDiag t`,

    for `μ`-a.e. `x` there is `δ > 0` such that every `u ∈ Uminus t` with `u ∈ V δ` satisfies
    `u • x ∈ [x]_m`,   `m = ⋁_{n ≥ 0} aDiag(t)^{-n} σ(P)`,

i.e. a small `Uminus t`-ball around `x` lies inside the atom of `x` for the past σ-algebra of
`P`.  This is the *tracking* property of Pisa's Chapter VII (Lemma 7.31), used to show that the
atoms of the coding σ-algebra are plaques.

## Structure of the proof

* `Nbd P η` is the `η`-neighbourhood of `⋃ i, frontier (P i)` in the `G`-action (exactly the set
  appearing in the hypothesis), and `Crosses P τ y` says that some `v ∈ V τ` moves `y` from a
  cell of `P` into a different cell.
* `crossing_mem`: if `Crosses P τ y` with `τ` small, then `y ∈ Nbd P (500 τ)`.  A path in `SL₃(ℝ)`
  from `1` to `v` inside `V (100 τ)` (`aeBall_V_path`) must meet `frontier (P i)`
  (`exists_mem_frontier_of_continuousOn`), and the inverse of the crossing point is in `V (500 τ)`
  (`aeBall_V_inv`).
* Since `μ (Nbd P η) ≤ c η`, Borel–Cantelli (`measure_iInter_iUnion_exp_eq_zero`) applied to the
  `a`-orbit of `Nbd P (500 e^{-α n})` gives a.e. `x` a time `N₀` after which the orbit is never
  crossed at scale `e^{-α n}`; for the finitely many earlier times one uses that a.e. point is
  uncrossed at *some* positive scale.
* Combining with the contraction hypothesis gives, for all `n`, the equality of the `P`-symbols
  of `a^n (u • x)` and `a^n x`, which by `mem_atom_of_forall_mem_iff` is exactly
  `u • x ∈ [x]_m`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Vocabulary: the thin boundary neighbourhood and the crossing relation -/

/-- `Nbd P η` is the `η`-neighbourhood (in the `G`-action) of the union of the frontiers of the
members of `P`.  This is exactly the set whose measure the "thin boundary" hypothesis bounds. -/
def Nbd {N : ℕ} (P : Fin N → Set X3) (η : ℝ) : Set X3 :=
  ⋃ i, (fun p : SL3 × X3 => p.1 • p.2) '' ((V η) ×ˢ (frontier (P i)))

/-- `Crosses P τ y` says that some `v ∈ V τ` moves `y` from a cell of `P` into a different cell:
i.e. the `τ`-ball around `y` is not contained in the `P`-symbol class of `y`. -/
def Crosses {N : ℕ} (P : Fin N → Set X3) (τ : ℝ) (y : X3) : Prop :=
  ∃ i, ∃ v : SL3, v ∈ V τ ∧ ((y ∈ P i ∧ v • y ∉ P i) ∨ (y ∉ P i ∧ v • y ∈ P i))

theorem mem_Nbd_iff {N : ℕ} {P : Fin N → Set X3} {η : ℝ} {y : X3} :
    y ∈ Nbd P η ↔ ∃ i, ∃ g ∈ V η, ∃ z ∈ frontier (P i), g • z = y := by
  simp only [Nbd, Set.mem_iUnion, Set.mem_image, Set.mem_prod]
  constructor
  · rintro ⟨i, p, hp, rfl⟩
    exact ⟨i, p.1, hp.1, p.2, hp.2, rfl⟩
  · rintro ⟨i, g, hg, z, hz, h⟩
    exact ⟨i, (g, z), ⟨hg, hz⟩, h⟩

theorem V_mono {s t : ℝ} (h : s ≤ t) : V s ⊆ V t :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

theorem Crosses_mono {N : ℕ} {P : Fin N → Set X3} {τ τ' : ℝ} (hle : τ ≤ τ') {y : X3}
    (h : Crosses P τ y) : Crosses P τ' y := by
  obtain ⟨i, v, hv, hcase⟩ := h
  exact ⟨i, v, V_mono hle hv, hcase⟩

/-! ## The crossing point of a path -/

/-- A continuous path `γ` in `SL₃(ℝ)` (on `[0,1]`) whose orbit of `y` starts inside `S` and ends
outside `S` must meet the frontier of `S`. -/
theorem exists_frontier_of_smul_path {S : Set X3} {γ : ℝ → SL3} {y : X3}
    (hγ : ContinuousOn γ (Set.Icc (0 : ℝ) 1)) (h0 : γ 0 • y ∈ S) (h1 : γ 1 • y ∉ S) :
    ∃ θ ∈ Set.Icc (0 : ℝ) 1, γ θ • y ∈ frontier S := by
  have hcont : ContinuousOn (fun θ : ℝ => γ θ • y) (Set.Icc (0 : ℝ) 1) :=
    ContinuousOn.smul hγ continuousOn_const
  exact exists_mem_frontier_of_continuousOn hcont h0 h1

/-! ## Crossing a thin boundary -/

/-- **Pisa 7.31 (geometric core).**  If `y` is crossed at a small scale `τ`, then `y` lies in the
`(500 τ)`-neighbourhood of the boundary family. -/
theorem crossing_mem {N : ℕ} {P : Fin N → Set X3} {τ : ℝ} (hτ : 0 < τ) (hτle : τ ≤ 1 / 800)
    {y : X3} (hy : Crosses P τ y) : y ∈ Nbd P (500 * τ) := by
  obtain ⟨i, v, hv, hcase⟩ := hy
  have hs : (0 : ℝ) < 100 * τ := by linarith
  have hs1 : 100 * τ ≤ 1 := by linarith
  have hs8 : 100 * τ ≤ 1 / 8 := by linarith
  have hv' : v ∈ V (100 * τ / 100) := by
    rw [show (100 : ℝ) * τ / 100 = τ by ring]
    exact hv
  obtain ⟨γ, hγcont, hγ0, hγ1, hγmem⟩ := aeBall_path hs hs1 hv'
  have hfront : ∃ θ ∈ Set.Icc (0 : ℝ) 1, γ θ • y ∈ frontier (P i) := by
    rcases hcase with ⟨hyP, hvP⟩ | ⟨hyP, hvP⟩
    · exact exists_frontier_of_smul_path hγcont (by rw [hγ0, one_smul]; exact hyP)
        (by rw [hγ1]; exact hvP)
    · obtain ⟨θ, hθ, hθf⟩ := exists_frontier_of_smul_path (S := (P i)ᶜ) hγcont
        (by rw [hγ0, one_smul]; exact hyP) (by rw [hγ1]; simpa using hvP)
      exact ⟨θ, hθ, by rwa [frontier_compl] at hθf⟩
  obtain ⟨θ, hθ, hθf⟩ := hfront
  have hinv : (γ θ)⁻¹ ∈ V (500 * τ) := by
    have h5 : (γ θ)⁻¹ ∈ V (5 * (100 * τ)) := aeBall_V_inv hs hs8 (hγmem θ hθ)
    rwa [show (5 : ℝ) * (100 * τ) = 500 * τ by ring] at h5
  rw [mem_Nbd_iff]
  exact ⟨i, (γ θ)⁻¹, hinv, γ θ • y, hθf, by rw [← mul_smul, inv_mul_cancel, one_smul]⟩

/-! ## The orbit of the diagonal action -/

theorem iterate_smul_eq (t : Fin 3 → ℝ) (n : ℕ) (y : X3) :
    (fun z : X3 => aDiag t • z)^[n] y = aDiag t ^ n • y := by
  induction n with
  | zero => simp
  | succ m ih => rw [Function.iterate_succ_apply', ih, ← mul_smul, pow_succ']

theorem orbit_smul_eq (t : Fin 3 → ℝ) (n : ℕ) (u : SL3) (x : X3) :
    (fun z : X3 => aDiag t • z)^[n] (u • x)
      = (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • ((fun z : X3 => aDiag t • z)^[n] x) := by
  rw [iterate_smul_eq t n (u • x), iterate_smul_eq t n x]
  simp only [mul_smul]
  rw [← mul_smul ((aDiag t ^ n)⁻¹) (aDiag t ^ n) x, inv_mul_cancel, one_smul]

/-! ## Elementary measure facts -/

/-- A nonnegative extended real number bounded by `ofReal ε` for every `ε > 0` is zero. -/
theorem eq_zero_of_forall_le_ofReal {x : ℝ≥0∞}
    (h : ∀ ε : ℝ, 0 < ε → x ≤ ENNReal.ofReal ε) : x = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  have hε' : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  rw [zero_add]
  simpa using h ((ε : ℝ)) hε'

/-! ## The atom criterion -/

/-- **Coding criterion.**  If two points are classified in the same way by every member of a family
`𝒞`, then each lies in the atom of the other for `generateFrom 𝒞`. -/
theorem mem_atom_of_forall_mem_iff {𝒞 : Set (Set X3)} {x y : X3}
    (h : ∀ C ∈ 𝒞, (y ∈ C ↔ x ∈ C)) : y ∈ atom (MeasurableSpace.generateFrom 𝒞) x := by
  set m := MeasurableSpace.generateFrom 𝒞 with hm
  have hiff : ∀ s, MeasurableSet[m] s → (x ∈ s ↔ y ∈ s) := by
    intro s hs
    induction s, hs using MeasurableSpace.generateFrom_induction (C := 𝒞) with
    | hC t ht _ => exact (h t ht).symm
    | empty => simp
    | compl t ht ih => simpa [Set.mem_compl_iff] using ih.not
    | iUnion f hf ihf => simp only [Set.mem_iUnion]; exact exists_congr fun n => ihf n
  exact Set.mem_sInter.mpr fun s hs => (hiff s hs.1).mp hs.2

theorem iSup_generateFrom_eq (S : ℕ → Set (Set X3)) :
    (⨆ n, MeasurableSpace.generateFrom (S n)) = MeasurableSpace.generateFrom (⋃ n, S n) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n => MeasurableSpace.generateFrom_le fun t ht => ?_
    exact MeasurableSpace.measurableSet_generateFrom (Set.subset_iUnion S n ht)
  · refine MeasurableSpace.generateFrom_le fun t ht => ?_
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ht
    exact le_iSup (fun n => MeasurableSpace.generateFrom (S n)) n t
      (MeasurableSpace.measurableSet_generateFrom hn)

/-! ## The main theorem -/

theorem ae_ball_in_atom {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {N : ℕ} (P : Fin N → Set Work.EKLContract.X3)
    (hmeas : ∀ i, MeasurableSet (P i))
    (hthin : ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η →
      μ (⋃ i, (fun p : Work.EKLContract.SL3 × Work.EKLContract.X3 => p.1 • p.2) ''
          ((Work.EKLContract.V η) ×ˢ (frontier (P i)))) ≤ ENNReal.ofReal (c * η))
    (hcontr : ∃ α : ℝ, 0 < α ∧
      ∀ (n : ℕ) (ρ : ℝ), 0 < ρ → ∀ u ∈ Work.EKLC6Core.Uminus t,
        u ∈ Work.EKLContract.V ρ →
          Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹ ∈
            Work.EKLContract.V (Real.exp (-(α * (n : ℝ))) * ρ)) :
    ∀ᵐ x ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ Work.EKLC6Core.Uminus t,
      (∀ i j, |u i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < δ) →
        u • x ∈ Work.EKLContract.atom
          (⨆ n : ℕ, MeasurableSpace.comap
            ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n])
            (MeasurableSpace.generateFrom (Set.range P)))
          x := by
  obtain ⟨c, hc, hthin⟩ := hthin
  obtain ⟨α, hα, hcontr⟩ := hcontr
  set a : X3 → X3 := fun y => aDiag t • y with ha
  have hamp : MeasurePreserving a μ μ := by rw [ha]; exact hmp
  have hNbd : ∀ η : ℝ, 0 < η → μ (Nbd P η) ≤ ENNReal.ofReal (c * η) := hthin
  -- `n₀` with `exp (-(α n)) ≤ 1/800` for `n ≥ n₀`
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
  -- measurable hulls of the thin neighbourhoods along the geometric scale
  classical
  choose T hTsub hTmeas hTμ using fun n : ℕ =>
    MeasureTheory.exists_measurable_superset μ (Nbd P (500 * Real.exp (-(α * (n : ℝ)))))
  have hTbound : ∀ n : ℕ,
      μ (T n) ≤ ENNReal.ofReal ((c * 500) * Real.exp (-(α * (n : ℝ)))) := by
    intro n
    rw [hTμ n]
    refine le_trans (hNbd _ (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    exact le_of_eq (by ring)
  have hAbound : ∀ n : ℕ,
      μ (a^[n] ⁻¹' T n) ≤ ENNReal.ofReal ((c * 500) * Real.exp (-(α * (n : ℝ)))) := by
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
  -- the scale at which a.e. point is uncrossed (the "good" set)
  set G : Set X3 := ⋃ k : ℕ, {y : X3 | ¬ Crosses P (1 / ((k : ℝ) + 801)) y} with hG
  have hcross_of_not_mem : ∀ k : ℕ, ∀ y : X3, y ∉ G → Crosses P (1 / ((k : ℝ) + 801)) y := by
    intro k y hy
    by_contra hcon
    refine hy ?_
    rw [hG]
    exact Set.mem_iUnion.mpr ⟨k, hcon⟩
  have hGsub : ∀ k : ℕ, Gᶜ ⊆ Nbd P (500 * (1 / ((k : ℝ) + 801))) := by
    intro k y hy
    refine crossing_mem (by positivity) ?_ (hcross_of_not_mem k y hy)
    refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 800) ?_
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hGnull : μ Gᶜ = 0 := by
    refine eq_zero_of_forall_le_ofReal fun ε hε => ?_
    obtain ⟨k, hk⟩ : ∃ k : ℕ, c * (500 / ((k : ℝ) + 801)) ≤ ε := by
      obtain ⟨m, hm⟩ := exists_nat_ge (c * 500 / ε + 1)
      refine ⟨m, ?_⟩
      have h1 : c * 500 / ε + 1 ≤ (m : ℝ) := hm
      have h2 : c * 500 / ε ≤ (m : ℝ) := by linarith
      have h3 : c * 500 ≤ (m : ℝ) * ε := by
        rw [div_le_iff₀ hε] at h2; linarith
      have h4 : c * (500 / ((m : ℝ) + 801)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 801)]
        nlinarith [h3, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)),
          (show (0 : ℝ) ≤ c * 500 by positivity)]
      exact h4
    refine le_trans (measure_mono (hGsub k)) ?_
    refine le_trans (hNbd _ (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    rw [show c * (500 * (1 / ((k : ℝ) + 801))) = c * (500 / ((k : ℝ) + 801)) by ring]
    exact hk
  -- a.e. point is in `G` at every time
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
  -- assembly
  filter_upwards [hBCae, hGae] with x hxBC hxG
  obtain ⟨N₀, hN₀⟩ := hxBC
  have hxG' : ∀ n : ℕ, ∃ k : ℕ, ¬ Crosses P (1 / ((k : ℝ) + 801)) (a^[n] x) := by
    intro n
    have h := hxG n
    rw [hG, Set.mem_iUnion] at h
    simpa only [Set.mem_ofPred_eq] using h
  choose kn hkn using hxG'
  have hknpos : ∀ n : ℕ, 0 < 1 / ((kn n : ℝ) + 801) := fun n => by positivity
  -- the minimum of the finitely many relevant scales
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
  intro u huU huV
  -- the scale at time `n` is never crossed
  have hfine : ∀ n : ℕ, ¬ Crosses P (Real.exp (-(α * (n : ℝ))) * δ) (a^[n] x) := by
    intro n
    rcases lt_or_ge n (max N₀ n₀ + 1) with hn | hn
    · -- early times
      have hle : δ ≤ (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n) := hδle n hn
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
      exact fun hc' => hkn n (Crosses_mono hscale hc')
    · -- late times
      have hnm : max N₀ n₀ ≤ n := by omega
      have hN0n : N₀ ≤ n := le_trans (le_max_left _ _) hnm
      have hn0n : n₀ ≤ n := le_trans (le_max_right _ _) hnm
      have hnotT : a^[n] x ∉ T n := fun hc' => hN₀ n hN0n hc'
      have hnotN : a^[n] x ∉ Nbd P (500 * Real.exp (-(α * (n : ℝ)))) :=
        fun hc' => hnotT (hTsub n hc')
      have hexp : Real.exp (-(α * (n : ℝ))) ≤ 1 / 800 := hn₀ n hn0n
      have hexppos : 0 < Real.exp (-(α * (n : ℝ))) := Real.exp_pos _
      have hscale : Real.exp (-(α * (n : ℝ))) * δ ≤ Real.exp (-(α * (n : ℝ))) := by
        nlinarith [Real.exp_pos (-(α * (n : ℝ)))]
      exact fun hc' => hnotN (crossing_mem hexppos hexp (Crosses_mono hscale hc'))
  -- the `P`-symbols of the two orbits agree at every time
  have hsym : ∀ (n : ℕ) (i : Fin N),
      ((fun y : X3 => aDiag t • y)^[n]) (u • x) ∈ P i ↔
        ((fun y : X3 => aDiag t • y)^[n]) x ∈ P i := by
    intro n i
    have hw : aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ V (Real.exp (-(α * (n : ℝ))) * δ) :=
      hcontr n δ hδpos u huU huV
    have hnot : ¬ Crosses P (Real.exp (-(α * (n : ℝ))) * δ) ((fun z : X3 => aDiag t • z)^[n] x) :=
      hfine n
    rw [orbit_smul_eq t n u x]
    by_cases hcase : ((fun z : X3 => aDiag t • z)^[n] x) ∈ P i
    · refine iff_of_true ?_ hcase
      by_contra hcon
      exact hnot ⟨i, _, hw, Or.inl ⟨hcase, hcon⟩⟩
    · refine iff_of_false ?_ hcase
      intro hcon
      exact hnot ⟨i, _, hw, Or.inr ⟨hcase, hcon⟩⟩
  -- conclude by the coding criterion
  have hsigma : (⨆ n : ℕ, MeasurableSpace.comap (a^[n])
        (MeasurableSpace.generateFrom (Set.range P)))
      = MeasurableSpace.generateFrom
          (⋃ n : ℕ, Set.preimage (a^[n]) '' (Set.range P)) := by
    rw [← iSup_generateFrom_eq]
    exact iSup_congr fun n => MeasurableSpace.comap_generateFrom
  rw [hsigma]
  refine mem_atom_of_forall_mem_iff ?_
  intro C hC
  obtain ⟨n, hCn⟩ := Set.mem_iUnion.mp hC
  simp only [Set.mem_image] at hCn
  obtain ⟨S, hS, hSC⟩ := hCn
  obtain ⟨i, rfl⟩ := hS
  rw [← hSC]
  exact hsym n i

end Work.EKLC6Core

end

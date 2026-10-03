import Mathlib
import Submission.Work.Parab.CoordData
import Submission.Work.Parab.LeftData
import Submission.Work.Parab.Setup
import Submission.Work.Parab.germ
import Submission.Work.Parab.basin_basic
import Submission.Work.Parab.basinEnters.petal_capture
import Submission.Work.Parab.basinCoord.exists_basin_coordinate
import Submission.Work.Parab.chartEstimate.chart_estimate
import Submission.Work.Parab.inversion.inverse_asymptotic
import Submission.Work.Parab.inversion.inverse_asymptotic_invOn
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn
import Submission.Work.Parab.coordData.cover_data
import Submission.Work.Parab.coordData.tau_seed_gen
import Submission.Work.Parab.coordData.leftCoordData_strong
import Submission.Work.Parab.coordData.hbig_of_asymp
import Submission.Work.Parab.coordData.cover_data_range
import Submission.Work.Parab.coordData.orbit_bound
import Submission.Work.Parab.coordData.wMap_run_asymptotic

/-!
# The maximal domain of the Ecalle coordinate `φ₀` (Shishikura A.3)

Given the ζ-plane left coordinate data `Work.Parab.LeftCoordData f D₀` we build the `φ`-side data
`Work.Parab.CoordData f D₀`: the coordinate `φ = τ₀ ∘ Φ⁻¹` transported along the dynamics to its
maximal domain

`Dφ = {w | ∃ n ≥ 0, w - n ∈ Q₀  and  f₀^j (φ₀ (w - n)) ∈ D₀ for j < n}`,

`φ w = f₀^n (φ₀ (w - n))`,

where `Q₀ = MandelDim.QLeft ξ₀` is a large sector contained in `Φ '' L` and `φ₀ = τ₀ ∘ Φ⁻¹` is the
seed.  The fields of `CoordData` are proved in `coordData_of_seed`; the analytic estimates on the
seed (membership in `L`, the orbit lower bound, the covering of the repelling cone) are separate
lemmas.

The target theorem `exists_CoordData` (Section 14) assembles the construction from

* `Work.Parab.coordData.leftCoordData_strong`: the ζ-plane left coordinate `dg`, *proper at
  infinity* on `dg.L`, with `dg.a = 1 - a` for the germ's quadratic coefficient `a`;
* `Work.Parab.inversion.inverse_asymptotic`: its inverse `τ = invOn dg.Φ dg.L` on a far sector,
  with the asymptotic `τ u = u + dg.a log(-u) + dg.b + o(1)`;
* `Work.Parab.coordData.tau_seed_gen`: on a larger sector `QLeft ξ₀` the seed is bounded below by
  `1/ρ`, lies in `dg.L` and stays there after one chart step;
* `Work.Parab.coordData.orbit_bound` (`horbit`) and `...hbig_of_asymp` (`hbig`): the chart orbit
  of `τ u` stays outside `2/ρ` with real part growing — this is what keeps the `f`-orbit inside
  `D₀` on the ends;
* `Work.Parab.coordData.cover_data_range`: the covering of the repelling cone with a prescribed
  vertex;
* `Work.Parab.coordData.wMap_run_asymptotic` and `...coord_ends_asymp`: the end asymptotic of the
  inverse coordinate along a chart run.

Note that the hypothesis `d` is *not* used: the intended ζ-plane coordinate is re-derived from
`hg` alone by `leftCoordData_strong` (the fields of `LeftCoordData` do not determine
`Φ` up to the properness needed here).
-/

namespace Work.Parab.coordData

open Complex Set Metric Filter
open scoped Topology

noncomputable section

/-! ## 1. Elementary geometry of the sectors `QLeft` -/

/-- `QLeft` is antitone in the vertex parameter: enlarging `ξ` moves the sector's vertex to the
left, so the set of admissible `w` shrinks. -/
theorem QLeft_anti {ξ ξ' : ℝ} (h : ξ ≤ ξ') : MandelDim.QLeft ξ' ⊆ MandelDim.QLeft ξ := by
  intro w hw
  rw [Work.Parab.QLeft_iff] at hw ⊢
  rcases eq_or_lt_of_le h with heq | hlt
  · subst heq; exact hw
  · set u : ℂ := w + (ξ : ℂ) with hu
    set u' : ℂ := w + (ξ' : ℂ) with hu'
    have hδ : 0 < ξ' - ξ := by linarith
    have hcast : ((ξ' : ℝ) : ℂ) = ((ξ : ℝ) : ℂ) + (((ξ' - ξ : ℝ)) : ℂ) := by push_cast; ring
    have hre : u.re = u'.re - (ξ' - ξ) := by
      rw [hu, hu', hcast]; simp only [Complex.add_re, Complex.ofReal_re]; ring
    have hnorm : ‖u'‖ ≤ ‖u‖ + (ξ' - ξ) := by
      have hu'u : u' = u + (((ξ' - ξ : ℝ)) : ℂ) := by rw [hu, hu', hcast]; ring
      rw [hu'u]
      have h1 := norm_add_le u (((ξ' - ξ : ℝ)) : ℂ)
      rwa [Complex.norm_real, Real.norm_of_nonneg hδ.le] at h1
    rw [hre]
    linarith

/-- `QLeft ξ` is closed under `w ↦ w - 1`. -/
theorem QLeft_sub_one (ξ : ℝ) {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ) :
    w - 1 ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff] at hw ⊢
  set u : ℂ := w + (ξ : ℂ) with hu
  have hsplit : (w - 1) + (ξ : ℂ) = u - 1 := by rw [hu]; ring
  rw [hsplit]
  have hnorm : ‖u‖ ≤ ‖u - 1‖ + 1 := by
    have h2 : u = (u - 1) + 1 := by ring
    calc ‖u‖ = ‖(u - 1) + 1‖ := congrArg norm h2
      _ ≤ ‖u - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖u - 1‖ + 1 := by simp
  have h2 : (u - 1).re = u.re - 1 := by simp
  rw [h2]
  linarith

/-- `QLeft ξ` is closed under all left translations by natural numbers. -/
theorem QLeft_sub_nat (ξ : ℝ) {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ) (k : ℕ) :
    w - (k : ℂ) ∈ MandelDim.QLeft ξ := by
  induction k with
  | zero => simpa using hw
  | succ i ih =>
      have h1 : w - ((i : ℕ) : ℂ) - 1 = w - ((i + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [← h1]
      exact QLeft_sub_one ξ ih

/-! ## 2. The seed and the maximal domain -/

/-- The seed `φ₀ = τ₀ ∘ τ` on the sector, where `τ = Φ⁻¹` is the inverse of the ζ-plane
coordinate. -/
def seed (τ : ℂ → ℂ) : ℂ → ℂ := fun w => MandelDim.tau0 (τ w)

/-- Shishikura's maximal domain: `w` is good if some left translate lies in the sector and the
forward orbit of the seed value from there stays in `D₀`. -/
def Good (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) (w : ℂ) : Prop :=
  ∃ n : ℕ, w - (n : ℂ) ∈ MandelDim.QLeft ξ₀ ∧
    ∀ j : ℕ, j < n → f^[j] (seed τ (w - (n : ℂ))) ∈ D₀

/-- The minimal witness for `Good`. -/
noncomputable def mIdx (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) (w : ℂ) : ℕ := by
  classical
  exact if h : Good f D₀ τ ξ₀ w then Nat.find h else 0

/-- The coordinate `φ` on its maximal domain. -/
noncomputable def coord (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) (w : ℂ) : ℂ :=
  f^[mIdx f D₀ τ ξ₀ w] (seed τ (w - (mIdx f D₀ τ ξ₀ w : ℂ)))

/-- The maximal domain `Dφ`. -/
def Dφ (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) : Set ℂ :=
  {w | Good f D₀ τ ξ₀ w}

/-- The coordinate, as a function. -/
def φ (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) : ℂ → ℂ := coord f D₀ τ ξ₀

theorem mIdx_spec {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ} {w : ℂ}
    (h : Good f D₀ τ ξ₀ w) :
    w - (mIdx f D₀ τ ξ₀ w : ℂ) ∈ MandelDim.QLeft ξ₀ ∧
      ∀ j : ℕ, j < mIdx f D₀ τ ξ₀ w →
        f^[j] (seed τ (w - (mIdx f D₀ τ ξ₀ w : ℂ))) ∈ D₀ := by
  classical
  rw [mIdx, dif_pos h]
  exact Nat.find_spec h

theorem mIdx_le {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ} {w : ℂ}
    (h : Good f D₀ τ ξ₀ w) {n : ℕ}
    (hn : w - (n : ℂ) ∈ MandelDim.QLeft ξ₀ ∧
      ∀ j : ℕ, j < n → f^[j] (seed τ (w - (n : ℂ))) ∈ D₀) :
    mIdx f D₀ τ ξ₀ w ≤ n := by
  classical
  rw [mIdx, dif_pos h]
  exact Nat.find_min' h hn

theorem coord_self (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) (w : ℂ) :
    coord f D₀ τ ξ₀ w = f^[mIdx f D₀ τ ξ₀ w] (seed τ (w - (mIdx f D₀ τ ξ₀ w : ℂ))) := rfl

/-! ## 3. The chart identity `τ₀ ∘ wMap = f ∘ τ₀` -/

theorem tau0_wMap (f : ℂ → ℂ) (y : ℂ) :
    MandelDim.tau0 (Work.FatouCoord.wMap f y) = f (MandelDim.tau0 y) := by
  have h0 : MandelDim.tau0 = Work.FatouCoord.chart := rfl
  rw [h0, Work.FatouCoord.wMap]
  rcases eq_or_ne (f (Work.FatouCoord.chart y)) 0 with h | h
  · rw [h]; simp
  · rw [Work.FatouCoord.chart_chart h]

theorem tau0_wMap_iterate (f : ℂ → ℂ) (k : ℕ) (y : ℂ) :
    MandelDim.tau0 ((Work.FatouCoord.wMap f)^[k] y) = f^[k] (MandelDim.tau0 y) := by
  induction k with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, tau0_wMap]

theorem tau0_tau0 (x : ℂ) : MandelDim.tau0 (MandelDim.tau0 x) = x := by
  have h0 : MandelDim.tau0 = Work.FatouCoord.chart := rfl
  rw [h0]
  rcases eq_or_ne x 0 with h | h
  · rw [h]; simp
  · rw [Work.FatouCoord.chart_chart h]

theorem norm_tau0 (x : ℂ) : ‖MandelDim.tau0 x‖ = 1 / ‖x‖ := by
  simp [MandelDim.tau0]

/-- The inverse chart identity: `τ₀ (f^[k] (τ₀ y)) = wMap^[k] y`. -/
theorem tau0_iterate (f : ℂ → ℂ) (k : ℕ) (y : ℂ) :
    MandelDim.tau0 (f^[k] (MandelDim.tau0 y)) = (Work.FatouCoord.wMap f)^[k] y := by
  have h := congrArg MandelDim.tau0 (tau0_wMap_iterate f k y)
  simpa [tau0_tau0] using h.symm

/-! ## 4. The seed hypotheses -/

/-- The facts about the seed that the maximal-domain construction uses: the chart iteration
`Φ (wMap y) = Φ y + 1` (conditional on `wMap y ∈ L`) and the maximality of `L` along the sector
(`Φ y = u ∈ QLeft ξ₀` with `y ∈ L` forces `wMap y ∈ L`). -/
structure SeedHyp (f : ℂ → ℂ) (D₀ : Set ℂ) (Φ : ℂ → ℂ) (L : Set ℂ) (τ : ℂ → ℂ)
    (ξ₀ : ℝ) : Prop where
  /-- the sector points are the image of `τ`, which is defined on the sector -/
  hspec : ∀ u ∈ MandelDim.QLeft ξ₀, Φ (τ u) = u
  /-- `τ` takes its values in `L` -/
  hmem : ∀ u ∈ MandelDim.QLeft ξ₀, τ u ∈ L
  /-- the successor of a sector point stays in `L` -/
  hwmap : ∀ u ∈ MandelDim.QLeft ξ₀, Work.FatouCoord.wMap f (τ u) ∈ L
  /-- `Φ` is injective on `L` -/
  hinj : Set.InjOn Φ L
  /-- the Abel equation in the ζ-plane -/
  habel : ∀ y ∈ L, Work.FatouCoord.wMap f y ∈ L →
    Φ (Work.FatouCoord.wMap f y) = Φ y + 1

/-- **The chart iteration.**  Along the sector, the chart iterates of `τ u` are the `τ`-values of
the translates of `u`. -/
theorem wMap_iterate_eq {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀) {u : ℂ} (hu : u ∈ MandelDim.QLeft ξ₀) {k : ℕ}
    (hk : ∀ j ≤ k, u + (j : ℂ) ∈ MandelDim.QLeft ξ₀) :
    (Work.FatouCoord.wMap f)^[k] (τ u) = τ (u + (k : ℂ)) := by
  have h : ∀ j ≤ k, (Work.FatouCoord.wMap f)^[j] (τ u) = τ (u + (j : ℂ)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ i ih =>
        intro hi
        have hiu : u + (i : ℂ) ∈ MandelDim.QLeft ξ₀ := hk i (by omega)
        have hiu' : u + ((i + 1 : ℕ) : ℂ) ∈ MandelDim.QLeft ξ₀ := hk (i + 1) (by omega)
        have his : u + ((i : ℕ) : ℂ) + 1 = u + ((i + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [Function.iterate_succ_apply', ih (by omega)]
        have hm : Work.FatouCoord.wMap f (τ (u + (i : ℂ))) ∈ L := hs.hwmap _ hiu
        have hval : Φ (Work.FatouCoord.wMap f (τ (u + (i : ℂ)))) = u + ((i + 1 : ℕ) : ℂ) := by
          rw [hs.habel _ (hs.hmem _ hiu) hm, hs.hspec _ hiu, his]
        exact hs.hinj hm (hs.hmem _ hiu') (by rw [hval, hs.hspec _ hiu'])
  exact h k le_rfl

/-- **The seed recursion.**  On the sector, `φ₀` transports along the dynamics: the seed value at
`u` is the `k`-th iterate of the seed value at `u - k`. -/
theorem seed_eq_iterate {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀) {u : ℂ} (hu : u ∈ MandelDim.QLeft ξ₀) (k : ℕ) :
    seed τ u = f^[k] (seed τ (u - (k : ℂ))) := by
  have hv : u - (k : ℂ) ∈ MandelDim.QLeft ξ₀ := QLeft_sub_nat ξ₀ hu k
  have hk : ∀ j ≤ k, (u - (k : ℂ)) + (j : ℂ) ∈ MandelDim.QLeft ξ₀ := by
    intro j hj
    have h1 : (u - (k : ℂ)) + (j : ℂ) = u - ((k - j : ℕ) : ℂ) := by
      rw [Nat.cast_sub hj]; ring
    rw [h1]; exact QLeft_sub_nat ξ₀ hu (k - j)
  have hiter := wMap_iterate_eq hs hv hk
  have h1 : (u - (k : ℂ)) + (k : ℂ) = u := by ring
  rw [h1] at hiter
  calc seed τ u = MandelDim.tau0 (τ u) := rfl
    _ = MandelDim.tau0 ((Work.FatouCoord.wMap f)^[k] (τ (u - (k : ℂ)))) := by rw [hiter]
    _ = f^[k] (MandelDim.tau0 (τ (u - (k : ℂ)))) := tau0_wMap_iterate f k _
    _ = f^[k] (seed τ (u - (k : ℂ))) := rfl

/-- **Well-definedness of `φ`.**  The value of `φ` at `w` is the same for all witnesses. -/
theorem coord_eq_of_witness {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ : ℝ} (hs : SeedHyp f D₀ Φ L τ ξ₀) {w : ℂ} (h : Good f D₀ τ ξ₀ w) {n : ℕ}
    (hn : w - (n : ℂ) ∈ MandelDim.QLeft ξ₀)
    (hD : ∀ j : ℕ, j < n → f^[j] (seed τ (w - (n : ℂ))) ∈ D₀) :
    coord f D₀ τ ξ₀ w = f^[n] (seed τ (w - (n : ℂ))) := by
  have hmle : mIdx f D₀ τ ξ₀ w ≤ n := mIdx_le h ⟨hn, hD⟩
  have hbase : w - (mIdx f D₀ τ ξ₀ w : ℂ) ∈ MandelDim.QLeft ξ₀ := (mIdx_spec h).1
  have hseed : seed τ (w - (mIdx f D₀ τ ξ₀ w : ℂ))
      = f^[n - mIdx f D₀ τ ξ₀ w] (seed τ (w - (n : ℂ))) := by
    have h := seed_eq_iterate hs hbase (n - mIdx f D₀ τ ξ₀ w)
    have h2 : (w - (mIdx f D₀ τ ξ₀ w : ℂ)) - ((n - mIdx f D₀ τ ξ₀ w : ℕ) : ℂ)
        = w - (n : ℂ) := by rw [Nat.cast_sub hmle]; ring
    rwa [h2] at h
  rw [coord_self, hseed, ← Function.iterate_add_apply, Nat.add_sub_of_le hmle]

/-! ## 5. The domain/propagator fields -/

theorem Q_sub_Dφ (f : ℂ → ℂ) (D₀ : Set ℂ) (τ : ℂ → ℂ) (ξ₀ : ℝ) :
    MandelDim.QLeft ξ₀ ⊆ Dφ f D₀ τ ξ₀ := by
  intro w hw
  exact ⟨0, by simpa using hw, by intro j hj; omega⟩

theorem exhaust_Dφ {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ} {w : ℂ}
    (h : w ∈ Dφ f D₀ τ ξ₀) : ∃ n : ℕ, w - (n : ℂ) ∈ MandelDim.QLeft ξ₀ :=
  ⟨mIdx f D₀ τ ξ₀ w, (mIdx_spec h).1⟩

theorem good_left {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ} {w : ℂ}
    (h : Good f D₀ τ ξ₀ w) : Good f D₀ τ ξ₀ (w - 1) := by
  rcases Nat.eq_zero_or_pos (mIdx f D₀ τ ξ₀ w) with hm | hm
  · have hw : w ∈ MandelDim.QLeft ξ₀ := by
      have := (mIdx_spec h).1
      simpa [hm] using this
    exact ⟨0, by simpa using QLeft_sub_one ξ₀ hw, by intro j hj; omega⟩
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
    have hspec := mIdx_spec h
    have hbase' : (w - 1) - (k : ℂ) = w - (mIdx f D₀ τ ξ₀ w : ℂ) := by
      rw [hk]; push_cast; ring
    refine ⟨k, ?_, ?_⟩
    · rw [hbase']; exact hspec.1
    · intro j hj
      rw [hbase']
      exact hspec.2 j (by omega)

theorem good_succ {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ} {w : ℂ}
    (h : Good f D₀ τ ξ₀ w) (hφ : coord f D₀ τ ξ₀ w ∈ D₀) : Good f D₀ τ ξ₀ (w + 1) := by
  have hspec := mIdx_spec h
  have hbase : (w + 1) - ((mIdx f D₀ τ ξ₀ w + 1 : ℕ) : ℂ) = w - (mIdx f D₀ τ ξ₀ w : ℂ) := by
    push_cast; ring
  refine ⟨mIdx f D₀ τ ξ₀ w + 1, ?_, ?_⟩
  · rw [hbase]; exact hspec.1
  · intro j hj
    rw [hbase]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
    · exact hspec.2 j hlt
    · rw [heq, ← coord_self]; exact hφ

theorem mem_D₀_of_succ {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ : ℝ} (hs : SeedHyp f D₀ Φ L τ ξ₀) (hQ : ∀ u ∈ MandelDim.QLeft ξ₀, seed τ u ∈ D₀)
    {w : ℂ} (h : Good f D₀ τ ξ₀ w) (h1 : Good f D₀ τ ξ₀ (w + 1)) :
    coord f D₀ τ ξ₀ w ∈ D₀ := by
  rcases Nat.eq_zero_or_pos (mIdx f D₀ τ ξ₀ (w + 1)) with hm | hm
  · have hw1 : w + 1 ∈ MandelDim.QLeft ξ₀ := by
      have := (mIdx_spec h1).1
      simpa [hm] using this
    have hw0 : w ∈ MandelDim.QLeft ξ₀ := by
      have h2 : (w + 1) - 1 = w := by ring
      rw [← h2]; exact QLeft_sub_one ξ₀ hw1
    have hmw : mIdx f D₀ τ ξ₀ w = 0 :=
      Nat.le_zero.mp (mIdx_le h ⟨by simpa using hw0, by intro j hj; omega⟩)
    rw [coord_self, hmw]
    simpa using hQ w hw0
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hm)
    have hspec := mIdx_spec h1
    have hwit : w - (k : ℂ) = (w + 1) - (mIdx f D₀ τ ξ₀ (w + 1) : ℂ) := by
      rw [hk]; push_cast; ring
    have hDk : ∀ j : ℕ, j < k → f^[j] (seed τ (w - (k : ℂ))) ∈ D₀ := by
      intro j hj
      rw [hwit]
      exact hspec.2 j (by omega)
    have hcoe := coord_eq_of_witness hs h (by rw [hwit]; exact hspec.1) hDk
    rw [hcoe, hwit]
    have hk' : k = mIdx f D₀ τ ξ₀ (w + 1) - 1 := by omega
    rw [hk']
    exact hspec.2 _ (by omega)

/-! ## 6. Holomorphy of the seed and its iterates -/

theorem differentiableOn_tau0 : DifferentiableOn ℂ MandelDim.tau0 {z : ℂ | z ≠ 0} := by
  have h : MandelDim.tau0 = fun z : ℂ => (-1 : ℂ) / z := rfl
  rw [h]
  exact (differentiableOn_const (-1)).div differentiableOn_id (fun z hz => hz)

theorem continuousAt_tau0 {x : ℂ} (hx : x ≠ 0) : ContinuousAt MandelDim.tau0 x := by
  have h : MandelDim.tau0 = fun z : ℂ => (-1 : ℂ) / z := rfl
  rw [h]
  exact continuousAt_const.div continuousAt_id hx

theorem continuousAt_seed {τ : ℂ → ℂ} {u : ℂ} (hτ : ContinuousAt τ u) (hne : τ u ≠ 0) :
    ContinuousAt (seed τ) u :=
  (continuousAt_tau0 hne).comp hτ

theorem differentiableAt_seed {τ : ℂ → ℂ} {u : ℂ} (hτ : DifferentiableAt ℂ τ u)
    (hne : τ u ≠ 0) : DifferentiableAt ℂ (seed τ) u :=
  (differentiableOn_tau0.differentiableAt (isOpen_ne.mem_nhds hne)).comp u hτ

theorem continuousAt_iterate_seed {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {u : ℂ} {j : ℕ}
    (hτ : ContinuousAt τ u) (hne : τ u ≠ 0)
    (hmid : ∀ i : ℕ, i < j → f^[i] (seed τ u) ∈ D₀)
    (hfD : DifferentiableOn ℂ f D₀) (hDo : IsOpen D₀) :
    ContinuousAt (fun w => f^[j] (seed τ w)) u := by
  induction j with
  | zero => simpa using continuousAt_seed hτ hne
  | succ i ih =>
      have hcont : ContinuousAt (fun w => f^[i] (seed τ w)) u := ih (fun k hk => hmid k (by omega))
      have hmem : f^[i] (seed τ u) ∈ D₀ := hmid i (by omega)
      have hfc : ContinuousAt f (f^[i] (seed τ u)) :=
        (hfD.differentiableAt (hDo.mem_nhds hmem)).continuousAt
      have hcomp : ContinuousAt (fun w : ℂ => f (f^[i] (seed τ w))) u :=
        ContinuousAt.comp (f := fun w : ℂ => f^[i] (seed τ w)) (g := f) (x := u) hfc hcont
      have hfe : (fun w : ℂ => f^[i + 1] (seed τ w)) = fun w => f (f^[i] (seed τ w)) := by
        funext w; rw [Function.iterate_succ_apply']
      rw [hfe]; exact hcomp

theorem differentiableAt_iterate_seed {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {u : ℂ} {j : ℕ}
    (hτ : DifferentiableAt ℂ τ u) (hne : τ u ≠ 0)
    (hmid : ∀ i : ℕ, i < j → f^[i] (seed τ u) ∈ D₀)
    (hfD : DifferentiableOn ℂ f D₀) (hDo : IsOpen D₀) :
    DifferentiableAt ℂ (fun w => f^[j] (seed τ w)) u := by
  induction j with
  | zero => simpa using differentiableAt_seed hτ hne
  | succ i ih =>
      have hdiff : DifferentiableAt ℂ (fun w => f^[i] (seed τ w)) u :=
        ih (fun k hk => hmid k (by omega))
      have hmem : f^[i] (seed τ u) ∈ D₀ := hmid i (by omega)
      have hfd : DifferentiableAt ℂ f (f^[i] (seed τ u)) := hfD.differentiableAt (hDo.mem_nhds hmem)
      have hcomp : DifferentiableAt ℂ (fun w : ℂ => f (f^[i] (seed τ w))) u :=
        DifferentiableAt.comp (x := u) (f := fun w : ℂ => f^[i] (seed τ w)) (g := f) hfd hdiff
      have hfe : (fun w : ℂ => f^[i + 1] (seed τ w)) = fun w => f (f^[i] (seed τ w)) := by
        funext w; rw [Function.iterate_succ_apply']
      rw [hfe]; exact hcomp

/-! ## 7. Openness of `Dφ` and holomorphy of `φ` -/

/-- The neighbourhood on which the minimal witness of `w` still works. -/
theorem eventually_good {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {W : Set ℂ} {ξ₀ ρ : ℝ}
    (hρ : 0 < ρ) (hWopen : IsOpen W) (hτdiff : DifferentiableOn ℂ τ W)
    (hQW : MandelDim.QLeft ξ₀ ⊆ W) (hτbig : ∀ u ∈ MandelDim.QLeft ξ₀, 1 / ρ ≤ ‖τ u‖)
    (hfD : DifferentiableOn ℂ f D₀) (hDo : IsOpen D₀) {w : ℂ} (hw : Good f D₀ τ ξ₀ w) :
    ∀ᶠ w' in 𝓝 w, w' - (mIdx f D₀ τ ξ₀ w : ℂ) ∈ MandelDim.QLeft ξ₀ ∧
      ∀ i : Fin (mIdx f D₀ τ ξ₀ w),
        f^[(i : ℕ)] (seed τ (w' - (mIdx f D₀ τ ξ₀ w : ℂ))) ∈ D₀ := by
  set m := mIdx f D₀ τ ξ₀ w with hm
  have hspec := mIdx_spec hw
  have hbase : w - (m : ℂ) ∈ MandelDim.QLeft ξ₀ := hspec.1
  have hmemW : w - (m : ℂ) ∈ W := hQW hbase
  have hne : τ (w - (m : ℂ)) ≠ 0 := by
    have h := hτbig _ hbase
    intro h0; rw [h0, norm_zero] at h; linarith [one_div_pos.mpr hρ]
  have hτc : ContinuousAt τ (w - (m : ℂ)) :=
    hτdiff.continuousOn.continuousAt (hWopen.mem_nhds hmemW)
  have h1 : {w' : ℂ | w' - (m : ℂ) ∈ MandelDim.QLeft ξ₀} ∈ 𝓝 w :=
    (continuousAt_id.sub continuousAt_const).preimage_mem_nhds
      ((isOpen_QLeft ξ₀).mem_nhds hbase)
  have h2 : {w' : ℂ | ∀ i : Fin m,
      f^[(i : ℕ)] (seed τ (w' - (m : ℂ))) ∈ D₀} ∈ 𝓝 w := by
    rw [← Filter.eventually_iff]
    rw [Filter.eventually_all]
    intro i
    have hcont : ContinuousAt (fun w' : ℂ => f^[(i : ℕ)] (seed τ (w' - (m : ℂ)))) w := by
      have h0 : (fun w' : ℂ => f^[(i : ℕ)] (seed τ (w' - (m : ℂ))))
          = (fun y => f^[(i : ℕ)] (seed τ y)) ∘ (fun w' => w' - (m : ℂ)) := rfl
      rw [h0]
      have hsub : ContinuousAt (fun w' : ℂ => w' - (m : ℂ)) w :=
        continuousAt_id.sub continuousAt_const
      exact ContinuousAt.comp (x := w) (f := fun w' : ℂ => w' - (m : ℂ))
        (g := fun y : ℂ => f^[(i : ℕ)] (seed τ y))
        (continuousAt_iterate_seed hτc hne
          (fun k hk => hspec.2 k (lt_trans hk i.isLt)) hfD hDo) hsub
    exact hcont.eventually (hDo.mem_nhds (hspec.2 i i.isLt))
  filter_upwards [h1, h2] with w' h1' h2'
  exact ⟨h1', h2'⟩

theorem isOpen_Dφ {f : ℂ → ℂ} {D₀ : Set ℂ} {τ : ℂ → ℂ} {W : Set ℂ} {ξ₀ ρ : ℝ}
    (hρ : 0 < ρ) (hWopen : IsOpen W) (hτdiff : DifferentiableOn ℂ τ W)
    (hQW : MandelDim.QLeft ξ₀ ⊆ W) (hτbig : ∀ u ∈ MandelDim.QLeft ξ₀, 1 / ρ ≤ ‖τ u‖)
    (hfD : DifferentiableOn ℂ f D₀) (hDo : IsOpen D₀) :
    IsOpen (Dφ f D₀ τ ξ₀) := by
  rw [isOpen_iff_mem_nhds]
  intro w hw
  obtain ⟨S, hS, hSspec⟩ :=
    (eventually_good hρ hWopen hτdiff hQW hτbig hfD hDo hw).exists_mem
  exact Filter.mem_of_superset hS (fun w' hw' =>
    ⟨mIdx f D₀ τ ξ₀ w, (hSspec w' hw').1, fun j hj => (hSspec w' hw').2 ⟨j, hj⟩⟩)

theorem φ_holo {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ} {W : Set ℂ}
    {ξ₀ ρ : ℝ} (hs : SeedHyp f D₀ Φ L τ ξ₀) (hρ : 0 < ρ)
    (hWopen : IsOpen W) (hτdiff : DifferentiableOn ℂ τ W)
    (hQW : MandelDim.QLeft ξ₀ ⊆ W) (hτbig : ∀ u ∈ MandelDim.QLeft ξ₀, 1 / ρ ≤ ‖τ u‖)
    (hfD : DifferentiableOn ℂ f D₀) (hDo : IsOpen D₀) :
    DifferentiableOn ℂ (φ f D₀ τ ξ₀) (Dφ f D₀ τ ξ₀) := by
  intro w hw
  set m := mIdx f D₀ τ ξ₀ w with hm
  have hspec := mIdx_spec hw
  have hbase : w - (m : ℂ) ∈ MandelDim.QLeft ξ₀ := hspec.1
  have hmemW : w - (m : ℂ) ∈ W := hQW hbase
  have hne : τ (w - (m : ℂ)) ≠ 0 := by
    have h := hτbig _ hbase
    intro h0; rw [h0, norm_zero] at h; linarith [one_div_pos.mpr hρ]
  have hτd : DifferentiableAt ℂ τ (w - (m : ℂ)) :=
    hτdiff.differentiableAt (hWopen.mem_nhds hmemW)
  have hdiff : DifferentiableAt ℂ (fun w' => f^[m] (seed τ (w' - (m : ℂ)))) w := by
    have h0 : (fun w' : ℂ => f^[m] (seed τ (w' - (m : ℂ))))
        = (fun y => f^[m] (seed τ y)) ∘ (fun w' => w' - (m : ℂ)) := rfl
    rw [h0]
    exact (differentiableAt_iterate_seed hτd hne (fun k hk => hspec.2 k hk) hfD hDo).comp w
      (differentiableAt_id.sub_const _)
  have hU : {w' : ℂ | w' - (m : ℂ) ∈ MandelDim.QLeft ξ₀ ∧
      ∀ i : Fin m, f^[(i : ℕ)] (seed τ (w' - (m : ℂ))) ∈ D₀} ∈ 𝓝 w :=
    Filter.eventually_iff.mp
      (eventually_good hρ hWopen hτdiff hQW hτbig hfD hDo hw)
  refine (hdiff.differentiableWithinAt).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hU] with w' hw'B hw'U
    exact coord_eq_of_witness hs hw'B hw'U.1 (fun j hj => hw'U.2 ⟨j, hj⟩)
  · exact coord_eq_of_witness hs hw hbase (fun j hj => hspec.2 j hj)


/-! ## 9. The ends (`|Im w|` large) -/

lemma log_le_half (c : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ t : ℝ, M ≤ t → c * (1 + Real.log (2 + t)) ≤ t / 2 := by
  have hK1 : 1 ≤ |c| + 1 := by
    have := abs_nonneg c; linarith
  refine ⟨max 1 (max (4 * c * (Real.log 2 + 1) + 1) (max (64 * (|c| + 1) ^ 2 + 1) 65)), ?_, ?_⟩
  · exact le_max_left _ _
  · intro t ht
    have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
    have hP : 4 * c * (Real.log 2 + 1) + 1 ≤ t :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
    have hQ : 64 * (|c| + 1) ^ 2 + 1 ≤ t :=
      le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) ht
    have hlog2pos : 0 < Real.log 2 + 1 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
    have hlog : Real.log (2 + t) ≤ Real.log 2 + 2 * Real.sqrt (1 + t) := by
      have h1 : Real.log (2 + t) ≤ Real.log (2 * (1 + t)) := by
        refine Real.log_le_log (by linarith) ?_
        linarith
      rw [Real.log_mul (by norm_num) (by linarith)] at h1
      have h2 : Real.log (1 + t) ≤ 2 * Real.sqrt (1 + t) := by
        have h3 := Real.log_le_rpow_div (show (0 : ℝ) ≤ 1 + t by linarith)
          (show (0 : ℝ) < 1 / 2 by norm_num)
        rw [show (1 + t) ^ ((1 : ℝ) / 2) = Real.sqrt (1 + t) from
          (Real.sqrt_eq_rpow (1 + t)).symm] at h3
        have h4 : Real.sqrt (1 + t) / (1 / 2) = 2 * Real.sqrt (1 + t) := by ring
        linarith [h3, h4.le]
      linarith
    have hs : Real.sqrt (1 + t) ≤ t / (8 * (|c| + 1)) := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_pow, le_div_iff₀ (by positivity)]
      nlinarith [hQ, hK1, abs_nonneg c, sq_nonneg (|c| + 1)]
    have h1 : c * (2 * Real.sqrt (1 + t)) ≤ t / 4 := by
      have h2 : c ≤ |c| + 1 := by
        have := le_abs_self c; linarith
      have h3 : c * (2 * Real.sqrt (1 + t)) ≤ (|c| + 1) * (2 * Real.sqrt (1 + t)) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
      have h4 : (|c| + 1) * (2 * Real.sqrt (1 + t)) ≤
          (|c| + 1) * (2 * (t / (8 * (|c| + 1)))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h5 : (|c| + 1) * (2 * (t / (8 * (|c| + 1)))) = t / 4 := by
        field_simp
        ring
      linarith [h3, h4, h5.le]
    have h2 : c * (Real.log 2 + 1) ≤ t / 4 := by
      by_cases hc : 0 ≤ c
      · have h3 : c * (Real.log 2 + 1) ≤ 4 * c * (Real.log 2 + 1) + 1 := by
          nlinarith [hlog2pos, hc]
        linarith [hP, h3]
      · have hc' : c < 0 := not_le.mp hc
        have h3 : c * (Real.log 2 + 1) ≤ 0 := by nlinarith [hlog2pos, hc']
        linarith
    by_cases hc : 0 ≤ c
    · have h5 : c * (1 + Real.log (2 + t)) ≤
          c * (1 + (Real.log 2 + 2 * Real.sqrt (1 + t))) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
      nlinarith [h5, h1, h2]
    · have hc' : c < 0 := not_le.mp hc
      have hpos : 0 ≤ 1 + Real.log (2 + t) := by
        have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + t); linarith
      have h5 : c * (1 + Real.log (2 + t)) ≤ 0 := by nlinarith [hpos, hc']
      linarith [ht1]

/-! ## 7b. Properness of `φ` near `0` (`preimage_far`) -/

/-- **`preimage_far`.**  `φ u = τ₀ (τ u)` is small on the sector only for `u` far out: the
inverse-coordinate asymptotic of `Φ` bounds `‖τ u‖` in terms of `‖u‖`, and
`‖τ₀ (τ u)‖ = 1 / ‖τ u‖`. -/
theorem preimage_far_of_asymp {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ} {ξ₀ ρ : ℝ} {a b : ℂ}
    (hρ : 0 < ρ)
    (hτbig : ∀ u ∈ MandelDim.QLeft ξ₀, 1 / ρ ≤ ‖τ u‖)
    (hτmem : ∀ u ∈ MandelDim.QLeft ξ₀, τ u ∈ L)
    (hτspec : ∀ u ∈ MandelDim.QLeft ξ₀, Φ (τ u) = u)
    (hΦasym : ∀ ε > 0, ∃ R : ℝ, ∀ x ∈ L, R < ‖x‖ →
      ‖Φ x - (x - a * Complex.log (-x) - b)‖ < ε) :
    ∀ B : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ u ∈ MandelDim.QLeft ξ₀,
      ‖MandelDim.tau0 (τ u)‖ < δ → B ≤ ‖u‖ := by
  intro B
  by_cases hB : B ≤ 0
  · refine ⟨1, one_pos, fun u _ _ => le_trans hB (norm_nonneg u)⟩
  · obtain ⟨RΦ₀, hRΦ₀⟩ := hΦasym 1 one_pos
    obtain ⟨M, hM1, hM⟩ := log_le_half ‖a‖
    set RΦ : ℝ := max RΦ₀ 1 with hRΦdef
    have hRΦ1 : 1 ≤ RΦ := le_max_right _ _
    have hRΦ0 : RΦ₀ ≤ RΦ := le_max_left _ _
    set B₁ : ℝ := max B 1 with hB₁def
    have hBle : B ≤ B₁ := le_max_left B 1
    set C : ℝ := max (max RΦ M) (2 * (B₁ + ‖a‖ * (Real.pi + 1) + ‖b‖ + 1)) with hCdef
    have hRΦleC : RΦ ≤ C := le_trans (le_max_left RΦ M) (le_max_left _ _)
    have hMleC : M ≤ C := le_trans (le_max_right RΦ M) (le_max_left _ _)
    have h2BleC : 2 * (B₁ + ‖a‖ * (Real.pi + 1) + ‖b‖ + 1) ≤ C := le_max_right _ _
    have hCpos : 0 < C := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_trans hRΦ1 hRΦleC)
    refine ⟨1 / (C + 1), by positivity, fun u hu hδ => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hnormu : ‖u‖ ≤ B₁ := le_trans (le_of_lt hcon) hBle
    have hτle : ‖τ u‖ ≤ C := by
      by_cases hcase : RΦ < ‖τ u‖
      · have hτ1 : 1 ≤ ‖τ u‖ := le_trans hRΦ1 (le_of_lt hcase)
        have h1 : ‖u - (τ u - a * Complex.log (-(τ u)) - b)‖ < 1 := by
          have h2 := hRΦ₀ (τ u) (hτmem u hu) (lt_of_le_of_lt hRΦ0 hcase)
          rwa [hτspec u hu] at h2
        have hlog : ‖Complex.log (-(τ u))‖ ≤ Real.log ‖τ u‖ + Real.pi := by
          have h9 := Work.Parab.inversion.norm_log_le (-(τ u)) (by simpa using hτ1)
          simpa using h9
        have h4 : ‖a * Complex.log (-(τ u)) + b‖ ≤ ‖a‖ * (Real.log ‖τ u‖ + Real.pi) + ‖b‖ := by
          have h4a : ‖a * Complex.log (-(τ u))‖ ≤ ‖a‖ * (Real.log ‖τ u‖ + Real.pi) := by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left hlog (norm_nonneg a)
          calc ‖a * Complex.log (-(τ u)) + b‖ ≤ ‖a * Complex.log (-(τ u))‖ + ‖b‖ :=
                norm_add_le _ _
            _ ≤ ‖a‖ * (Real.log ‖τ u‖ + Real.pi) + ‖b‖ := by linarith
        have h1' : ‖(τ u - a * Complex.log (-(τ u)) - b) - u‖ < 1 := by
          rw [norm_sub_rev]
          exact h1
        have h5 : ‖τ u‖ ≤ ‖u‖ + (1 + ‖a‖ * (Real.log ‖τ u‖ + Real.pi) + ‖b‖) := by
          have h6 : ‖τ u‖ ≤ ‖u‖ + ‖τ u - u‖ := by
            have h := norm_add_le u (τ u - u)
            have he : u + (τ u - u) = τ u := by ring
            rwa [he] at h
          have h7 : ‖τ u - u‖ ≤ 1 + ‖a * Complex.log (-(τ u)) + b‖ := by
            have h8 : τ u - u = ((τ u - a * Complex.log (-(τ u)) - b) - u)
                + (a * Complex.log (-(τ u)) + b) := by ring
            rw [h8]
            calc ‖((τ u - a * Complex.log (-(τ u)) - b) - u)
                  + (a * Complex.log (-(τ u)) + b)‖
                ≤ ‖(τ u - a * Complex.log (-(τ u)) - b) - u‖
                  + ‖a * Complex.log (-(τ u)) + b‖ := norm_add_le _ _
              _ ≤ 1 + ‖a * Complex.log (-(τ u)) + b‖ := by linarith [h1']
          linarith [h6, h7, h4]
        by_cases hMτ : M ≤ ‖τ u‖
        · have hlogle : ‖a‖ * Real.log ‖τ u‖ ≤ ‖τ u‖ / 2 := by
            have h6 : Real.log ‖τ u‖ ≤ 1 + Real.log (2 + ‖τ u‖) := by
              have h7 : 0 < ‖τ u‖ :=
                lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) (le_trans hM1 hMτ)
              have h8 : Real.log ‖τ u‖ ≤ Real.log (2 + ‖τ u‖) :=
                Real.log_le_log h7 (by linarith)
              linarith
            have h9 := hM ‖τ u‖ hMτ
            nlinarith [norm_nonneg a]
          have h10 : ‖a‖ * (Real.log ‖τ u‖ + Real.pi) ≤ ‖τ u‖ / 2 + ‖a‖ * Real.pi := by
            nlinarith [hlogle]
          have h11 : ‖τ u‖ ≤ ‖u‖ + (1 + (‖τ u‖ / 2 + ‖a‖ * Real.pi) + ‖b‖) := by
            linarith [h5, h10]
          have h12 : ‖τ u‖ / 2 ≤ ‖u‖ + (1 + ‖a‖ * Real.pi + ‖b‖) := by linarith [h11]
          have h13 : ‖τ u‖ ≤ 2 * (‖u‖ + (1 + ‖a‖ * Real.pi + ‖b‖)) := by linarith [h12]
          have h14 : ‖u‖ + (1 + ‖a‖ * Real.pi + ‖b‖) ≤ B₁ + ‖a‖ * (Real.pi + 1) + ‖b‖ + 1 := by
            nlinarith [hnormu, norm_nonneg a, norm_nonneg b]
          linarith [h13, h14, h2BleC]
        · rw [not_le] at hMτ
          linarith [le_of_lt hMτ, hMleC]
      · rw [not_lt] at hcase
        exact le_trans hcase hRΦleC
    have hτpos : 0 < ‖τ u‖ := lt_of_lt_of_le (div_pos one_pos hρ) (hτbig u hu)
    have hC1 : 1 / C ≤ ‖MandelDim.tau0 (τ u)‖ := by
      rw [norm_tau0]
      exact one_div_le_one_div_of_le hτpos hτle
    have hlt : 1 / C < 1 / (C + 1) := lt_of_le_of_lt hC1 hδ
    have hcontra : 1 / (C + 1) < 1 / C := one_div_lt_one_div_of_lt hCpos (by linarith)
    linarith [hlt, hcontra]


/-- The remaining fields of `MandelDim.CoordData`, from the seed data. -/
theorem coordData_of_seed {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {W : Set ℂ} {ξ₀ ρ η₀ : ℝ} {a b : ℂ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀)
    (hξ₀ : 0 < ξ₀) (hρ : 0 < ρ) (hη₀ : 0 < η₀)
    (hball : Metric.ball 0 ρ ⊆ D₀)
    (hDo : IsOpen D₀) (hfD : DifferentiableOn ℂ f D₀)
    (hWopen : IsOpen W) (hτdiff : DifferentiableOn ℂ τ W)
    (hQW : MandelDim.QLeft ξ₀ ⊆ W)
    (hτbig : ∀ u ∈ MandelDim.QLeft ξ₀, 1 / ρ ≤ ‖τ u‖)
    (hseedD : ∀ u ∈ MandelDim.QLeft ξ₀, seed τ u ∈ D₀)
    (hasymp : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₀, R < ‖u‖ →
      ‖τ u - (u + a * Complex.log (-u) + b)‖ < ε)
    (hΦasym : ∀ ε > 0, ∃ R : ℝ, ∀ x ∈ L, R < ‖x‖ →
      ‖Φ x - (x - a * Complex.log (-x) - b)‖ < ε)
    (h : ℂ → ℂ) (ag : ℂ) (rg Ag Ag' : ℝ)
    (hbP : Work.FatouCoord.ParabolicBounds f h ag rg Ag Ag') (haeq : a = 1 - ag)
    (hendasym : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < |w.im| →
      ‖MandelDim.tau0 (coord f D₀ τ ξ₀ w) - (w + (1 - ag) * Complex.log (-w) + b)‖ < ε)
    (hcover : ∃ ρc : ℝ, 0 < ρc ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρc →
      |z.arg| ≤ Real.pi / 2 + Real.pi / 12 →
        ∃ w ∈ MandelDim.QLeft ξ₀, coord f D₀ τ ξ₀ w = z)
    (hends : ∀ w : ℂ, η₀ < |w.im| → w ∈ Dφ f D₀ τ ξ₀ ∧
      coord f D₀ τ ξ₀ w ∈ MandelDim.ParabolicBasin f D₀) :
    Nonempty (Work.Parab.CoordData f D₀) := by
  have hm0_of_mem : ∀ {w : ℂ}, w ∈ MandelDim.QLeft ξ₀ → mIdx f D₀ τ ξ₀ w = 0 := by
    intro w hw
    have hG : Good f D₀ τ ξ₀ w := ⟨0, by simpa using hw, by intro j hj; omega⟩
    have hwit : w - ((0 : ℕ) : ℂ) ∈ MandelDim.QLeft ξ₀ ∧
        ∀ j : ℕ, j < 0 → f^[j] (seed τ (w - ((0 : ℕ) : ℂ))) ∈ D₀ :=
      ⟨by simpa using hw, by intro j hj; omega⟩
    exact Nat.le_zero.mp (mIdx_le hG hwit)
  have hcoordQ : ∀ {w : ℂ} (hw : w ∈ MandelDim.QLeft ξ₀),
      coord f D₀ τ ξ₀ w = seed τ w := by
    intro w hw
    rw [coord_self, hm0_of_mem hw]
    simp
  refine ⟨{
    ξ₀ := ξ₀
    φ := φ f D₀ τ ξ₀
    Dφ := Dφ f D₀ τ ξ₀
    η₀ := η₀
    ξ₀_pos := hξ₀
    Dφ_open := isOpen_Dφ hρ hWopen hτdiff hQW hτbig hfD hDo
    Q_sub := Q_sub_Dφ f D₀ τ ξ₀
    exhaust := fun w hw => exhaust_Dφ hw
    left_inv := fun w hw => good_left hw
    succ_iff := ?_
    φ_holo := φ_holo hs hρ hWopen hτdiff hQW hτbig hfD hDo
    Q_maps := fun u hu => by
      change coord f D₀ τ ξ₀ u ∈ D₀
      rw [hcoordQ hu]
      exact hseedD u hu
    φ_abel := ?_
    φ_inj := ?_
    φ_asymp := ?_
    ag := ag
    bEnd := b
    φ_asymp_ends := by
      intro ε hε
      obtain ⟨R, hR⟩ := hendasym ε hε
      exact ⟨R, fun w hw => hR w hw⟩
    hbond := ⟨h, rg, Ag, Ag', hbP⟩
    preimage_far := by
      have hfar := preimage_far_of_asymp (Φ := Φ) (L := L) (τ := τ) (ξ₀ := ξ₀) (ρ := ρ)
        (a := a) (b := b) hρ hτbig (fun u hu => hs.hmem u hu) (fun u hu => hs.hspec u hu) hΦasym
      intro B
      obtain ⟨δ, hδpos, hδ⟩ := hfar B
      refine ⟨δ, hδpos, fun u hu hlt => hδ u hu ?_⟩
      have h1 : φ f D₀ τ ξ₀ u = MandelDim.tau0 (τ u) := by
        rw [show φ f D₀ τ ξ₀ u = coord f D₀ τ ξ₀ u from rfl, hcoordQ hu]
        rfl
      rwa [h1] at hlt
    cover := hcover
    ends_sub := hends }⟩
  · intro w hw
    constructor
    · intro hw1
      exact mem_D₀_of_succ hs hseedD hw hw1
    · intro hφ
      exact good_succ hw hφ
  · intro w hw hw1
    have hmem : coord f D₀ τ ξ₀ w ∈ D₀ := mem_D₀_of_succ hs hseedD hw hw1
    have hspec := mIdx_spec hw
    have hw1' : Good f D₀ τ ξ₀ (w + 1) := good_succ hw hmem
    have hcoe : coord f D₀ τ ξ₀ (w + 1)
        = f^[mIdx f D₀ τ ξ₀ w + 1] (seed τ (w - (mIdx f D₀ τ ξ₀ w : ℂ))) := by
      have hb : (w + 1) - (((mIdx f D₀ τ ξ₀ w + 1 : ℕ)) : ℂ)
          = w - (mIdx f D₀ τ ξ₀ w : ℂ) := by push_cast; ring
      have h0 := coord_eq_of_witness (n := mIdx f D₀ τ ξ₀ w + 1) hs hw1'
        (by rw [hb]; exact hspec.1)
        (by
          intro j hj
          rw [hb]
          rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
          · exact hspec.2 j hlt
          · rw [heq, ← coord_self]; exact hmem)
      rwa [hb] at h0
    have hgoal : coord f D₀ τ ξ₀ (w + 1) = f (coord f D₀ τ ξ₀ w) := by
      rw [hcoe, coord_self, Function.iterate_succ_apply']
    exact hgoal
  · intro u hu u' hu' heq
    have h1 : seed τ u = seed τ u' := by
      rw [← hcoordQ hu, ← hcoordQ hu']; exact heq
    have h2 : τ u = τ u' := by
      have := congrArg MandelDim.tau0 h1
      simpa [seed, tau0_tau0] using this
    rw [← hs.hspec u hu, ← hs.hspec u' hu', h2]
  · refine ⟨a, b, fun ε hε => ?_⟩
    obtain ⟨R, hR⟩ := hasymp ε hε
    refine ⟨max R 0, fun w hw hRw => ?_⟩
    have h1 : MandelDim.tau0 (φ f D₀ τ ξ₀ w) = τ w := by
      rw [show φ f D₀ τ ξ₀ w = coord f D₀ τ ξ₀ w from rfl, hcoordQ hw]
      simp [seed, tau0_tau0]
    rw [h1]
    exact hR w hw (lt_of_le_of_lt (le_max_left _ _) hRw)

/-! ## 10. The successor step and its iteration -/

/-- The coordinate of the successor: `φ (x+1) = f (φ x)` whenever both sides are defined. -/
theorem coord_succ {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ} {ξ₀ : ℝ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀) {x : ℂ} (hx : Good f D₀ τ ξ₀ x)
    (hm : coord f D₀ τ ξ₀ x ∈ D₀) :
    coord f D₀ τ ξ₀ (x + 1) = f (coord f D₀ τ ξ₀ x) := by
  have hspec := mIdx_spec hx
  have hw1 : Good f D₀ τ ξ₀ (x + 1) := good_succ hx hm
  have hb : (x + 1) - (((mIdx f D₀ τ ξ₀ x + 1 : ℕ)) : ℂ)
      = x - (mIdx f D₀ τ ξ₀ x : ℂ) := by push_cast; ring
  have h0 := coord_eq_of_witness (n := mIdx f D₀ τ ξ₀ x + 1) hs hw1
    (by rw [hb]; exact hspec.1)
    (by
      intro j hj
      rw [hb]
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
      · exact hspec.2 j hlt
      · rw [heq, ← coord_self]; exact hm)
  have hgoal : coord f D₀ τ ξ₀ (x + 1) = f (coord f D₀ τ ξ₀ x) := by
    rw [h0, coord_self, Function.iterate_succ_apply', hb]
  exact hgoal

/-- Iterating the successor step: if the iterates of `φ w` stay in `D₀`, then `φ (w+K)` is the
`K`-th iterate. -/
theorem good_add_of_iterate {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ : ℝ} (hs : SeedHyp f D₀ Φ L τ ξ₀) {w : ℂ} (hw : Good f D₀ τ ξ₀ w) {K : ℕ}
    (hD : ∀ j : ℕ, j < K → f^[j] (coord f D₀ τ ξ₀ w) ∈ D₀) :
    Good f D₀ τ ξ₀ (w + (K : ℂ)) ∧
      coord f D₀ τ ξ₀ (w + (K : ℂ)) = f^[K] (coord f D₀ τ ξ₀ w) := by
  induction K with
  | zero => exact ⟨by simpa using hw, by simp⟩
  | succ i ih =>
      have hD' : ∀ j : ℕ, j < i → f^[j] (coord f D₀ τ ξ₀ w) ∈ D₀ := fun j hj => hD j (by omega)
      obtain ⟨hg, hc⟩ := ih hD'
      have hmem : coord f D₀ τ ξ₀ (w + (i : ℂ)) ∈ D₀ := by
        rw [hc]; exact hD i (by omega)
      have hsucc : coord f D₀ τ ξ₀ ((w + (i : ℂ)) + 1) = f (coord f D₀ τ ξ₀ (w + (i : ℂ))) :=
        coord_succ hs hg hmem
      have hgood : Good f D₀ τ ξ₀ ((w + (i : ℂ)) + 1) := good_succ hg hmem
      have h1 : w + ((i + 1 : ℕ) : ℂ) = (w + (i : ℂ)) + 1 := by push_cast; ring
      refine ⟨by rwa [h1], ?_⟩
      rw [h1, hsucc, hc, Function.iterate_succ_apply']

/-! ## 11. The basin is closed under taking backward iterates -/

theorem mem_basin_of_iterate {f : ℂ → ℂ} {D₀ : Set ℂ} {z z' : ℂ} {K : ℕ}
    (hD : IsOpen D₀) (hdiff : DifferentiableOn ℂ f D₀)
    (hz : z ∈ MandelDim.ParabolicBasin f D₀) (hK : f^[K] z' = z)
    (hmid : ∀ j : ℕ, j ≤ K → f^[j] z' ∈ D₀) :
    z' ∈ MandelDim.ParabolicBasin f D₀ := by
  classical
  obtain ⟨U, hU, hUmap, hUconv⟩ := hz
  have hcont : ∀ j : ℕ, j ≤ K → ContinuousAt (f^[j]) z' := by
    intro j hj
    induction j with
    | zero => simpa using continuousAt_id
    | succ i ih =>
        have hi : i ≤ K := by omega
        have hfi : ContinuousAt (f^[i]) z' := ih hi
        have hfd : ContinuousAt f (f^[i] z') :=
          (hdiff.differentiableAt (hD.mem_nhds (hmid i hi))).continuousAt
        have hcomp : ContinuousAt (fun x => f (f^[i] x)) z' := hfd.comp hfi
        have he : (f^[i + 1]) = fun x => f (f^[i] x) := by
          funext x; rw [Function.iterate_succ_apply']
        rw [he]; exact hcomp
  have h1 : {x : ℂ | ∀ j : Fin (K + 1), f^[(j : ℕ)] x ∈ D₀} ∈ 𝓝 z' := by
    rw [← Filter.eventually_iff, Filter.eventually_all]
    intro j
    exact (hcont (j : ℕ) (by omega)).preimage_mem_nhds (hD.mem_nhds (hmid (j : ℕ) (by omega)))
  have h2 : {x : ℂ | f^[K] x ∈ U} ∈ 𝓝 z' := by
    have := (hcont K le_rfl).preimage_mem_nhds (by rw [hK]; exact hU)
    exact this
  refine ⟨{x : ℂ | (∀ j : Fin (K + 1), f^[(j : ℕ)] x ∈ D₀) ∧ f^[K] x ∈ U},
    Filter.inter_mem h1 h2, ?_, ?_⟩
  · intro n x hx
    by_cases hn : n ≤ K
    · exact hx.1 ⟨n, by omega⟩
    · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (le_of_lt (Nat.lt_of_not_le hn))
      have h3 : f^[n] x = f^[m] (f^[K] x) := by
        rw [hm, Nat.add_comm, Function.iterate_add_apply]
      rw [h3]
      exact hUmap m hx.2
  · rw [Metric.tendstoUniformlyOn_iff] at hUconv ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hUconv ε hε)
    refine eventually_atTop.mpr ⟨N + K, fun n hn x hx => ?_⟩
    have hnK : K ≤ n := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hnK
    have h3 : f^[n] x = f^[m] (f^[K] x) := by
      rw [hm, Nat.add_comm, Function.iterate_add_apply]
    rw [h3]
    refine hN m ?_ (f^[K] x) hx.2
    omega

/-! ## 12. A logarithmic growth lemma for the imaginary part of the orbit -/

/-- For any `m₀`, `T` and `D > 0`, the expression `m₀ + j/2 - c (1 + log (2+j+D))` eventually
exceeds `T`.  (Used to produce the backward extension reaching the attracting petal.) -/
lemma exists_iterate_re_gt (c m₀ T : ℝ) (hc : 0 ≤ c) {D : ℝ} (hD : 0 < D) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j →
      T < m₀ + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + D)) := by
  obtain ⟨M₁, hM₁1, hM₁⟩ := log_le_half (8 * c)
  refine ⟨⌈max M₁ (max 1 ((16 / 7) * (c * (1 + Real.log (2 + D)) + T - m₀) + 1))⌉₊ + 1,
    fun j hj => ?_⟩
  have hjR : max M₁ (max 1 ((16 / 7) * (c * (1 + Real.log (2 + D)) + T - m₀) + 1)) ≤ (j : ℝ) := by
    have h1 : (⌈max M₁ (max 1 ((16 / 7) * (c * (1 + Real.log (2 + D)) + T - m₀) + 1))⌉₊ : ℝ)
        ≤ (j : ℝ) := by
      exact_mod_cast Nat.le_of_succ_le hj
    have h2 := Nat.le_ceil (max M₁ (max 1 ((16 / 7) * (c * (1 + Real.log (2 + D)) + T - m₀) + 1)))
    linarith
  have hjM₁ : M₁ ≤ (j : ℝ) := le_trans (le_max_left _ _) hjR
  have hjB : (16 / 7) * (c * (1 + Real.log (2 + D)) + T - m₀) + 1 ≤ (j : ℝ) :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hjR
  have h1 : c * (1 + Real.log (2 + (j : ℝ) + D))
      ≤ c * (1 + Real.log (2 + D)) + (j : ℝ) / 16 := by
    have h2 : Real.log (2 + (j : ℝ) + D) ≤ Real.log (2 + D) + Real.log (1 + (j : ℝ)) := by
      have h3 : (0 : ℝ) < 2 + D := by linarith
      have h4 : 2 + (j : ℝ) + D ≤ (2 + D) * (1 + (j : ℝ)) := by nlinarith
      calc Real.log (2 + (j : ℝ) + D) ≤ Real.log ((2 + D) * (1 + (j : ℝ))) :=
            Real.log_le_log (by linarith) h4
        _ = Real.log (2 + D) + Real.log (1 + (j : ℝ)) := Real.log_mul (by linarith) (by linarith)
    have h5 : c * (1 + Real.log (2 + (j : ℝ))) ≤ (j : ℝ) / 16 := by
      have h6 := hM₁ (j : ℝ) hjM₁
      have h7 : c * (1 + Real.log (2 + (j : ℝ)))
          = (8 * c * (1 + Real.log (2 + (j : ℝ)))) / 8 := by ring
      rw [h7]
      linarith
    have h6 : Real.log (1 + (j : ℝ)) ≤ 1 + Real.log (2 + (j : ℝ)) := by
      have h7 := Real.log_le_log (by linarith : (0 : ℝ) < 1 + (j : ℝ))
        (by linarith : 1 + (j : ℝ) ≤ 2 + (j : ℝ))
      linarith
    have h7 : c * Real.log (1 + (j : ℝ)) ≤ c * (1 + Real.log (2 + (j : ℝ))) :=
      mul_le_mul_of_nonneg_left h6 hc
    nlinarith [h2, h5, h7, hc]
  nlinarith [h1, hjB]



/-! ## 13. The ends -/


/-- `⌈x⌉ ≤ x + 1` for `x ≥ -1`. -/
lemma ceil_le_add_one_of_le {x : ℝ} (hx : -1 ≤ x) : ((Nat.ceil x : ℕ) : ℝ) ≤ x + 1 := by
  by_cases h : x ≤ 0
  · have h0 : Nat.ceil x = 0 := Nat.le_zero.mp (Nat.ceil_le.mpr (by simpa using h))
    rw [h0]; push_cast; linarith
  · push_neg at h
    exact le_of_lt (Nat.ceil_lt_add_one h.le)

/-- Sector membership from the closed half-plane `Re z ≤ -ξ`, as long as `z + ξ ≠ 0`. -/
lemma mem_QLeft_of_re_le {ξ : ℝ} {z : ℂ} (h : z.re ≤ -ξ) (hne : z + (ξ : ℂ) ≠ 0) :
    z ∈ MandelDim.QLeft ξ := by
  rw [Work.Parab.QLeft_iff]
  have h1 : (z + (ξ : ℂ)).re ≤ 0 := by
    have h1' : (z + (ξ : ℂ)).re = z.re + ξ := by simp
    rw [h1']; linarith
  have h2 : 0 < ‖z + (ξ : ℂ)‖ := norm_pos_iff.mpr hne
  linarith

/-- **The strip case of the ends argument.**  If `Re w ≥ -ξ₀ - 1` then the witness
`u = w - (⌈Re w + ξ₀⌉ + 1)` satisfies `-ξ₀ - 2 < Re u ≤ -ξ₀ - 1`, hence the strip bound
`‖u‖ ≤ |Im u| + ξ₀ + 3`; the orbit lower bound `hbig`/`horbit` then shows that the seed orbit
stays in `ball 0 ρ`, and it can be followed until the attracting petal is reached. -/
theorem ends_strip {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ ρ Mp c η : ℝ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀) (hξ₀ : 0 < ξ₀) (hρ : 0 < ρ) (hMp : 0 < Mp) (hη : 0 < η)
    (hc : 0 ≤ c)
    (hball : Metric.ball 0 ρ ⊆ D₀)
    (hpetalbasin : Work.FatouCoord.Petal ρ Mp ⊆ MandelDim.ParabolicBasin f D₀)
    (hbig : ∀ u ∈ MandelDim.QLeft ξ₀, η ≤ |u.im| → ‖u‖ ≤ |u.im| + ξ₀ + 3 →
      2 * (1 / ρ) + c * (1 + Real.log (2 + ‖τ u‖)) ≤ |(τ u).im|)
    (horbit : ∀ ζ : ℂ, 2 * (1 / ρ) + c * (1 + Real.log (2 + ‖ζ‖)) ≤ |ζ.im| → ∀ j : ℕ,
      2 * (1 / ρ) ≤ ‖(Work.FatouCoord.wMap f)^[j] ζ‖ ∧
      ((Work.FatouCoord.wMap f)^[j] ζ).re ≥
        min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)))
    (hDopen : IsOpen D₀) (hfD : DifferentiableOn ℂ f D₀) :
    ∀ w : ℂ, η < |w.im| → -ξ₀ - 1 ≤ w.re → w ∈ Dφ f D₀ τ ξ₀ ∧
      coord f D₀ τ ξ₀ w ∈ MandelDim.ParabolicBasin f D₀ := by
  intro w hw hwr0
  set n : ℕ := Nat.ceil (w.re + ξ₀) + 1 with hn
  set u : ℂ := w - (n : ℂ) with hu
  have hceil : w.re + ξ₀ ≤ ((Nat.ceil (w.re + ξ₀) : ℕ) : ℝ) := Nat.le_ceil _
  have hure : u.re = w.re - ((n : ℕ) : ℝ) := by
    rw [hu]; simp
  have hre : u.re ≤ -ξ₀ - 1 := by
    have h1 : w.re + ξ₀ + 1 ≤ ((n : ℕ) : ℝ) := by
      have h2 := Nat.le_ceil (w.re + ξ₀)
      rw [hn]
      push_cast
      linarith
    linarith
  have hre_lo : -ξ₀ - 2 ≤ u.re := by
    have h3 : ((Nat.ceil (w.re + ξ₀) : ℕ) : ℝ) ≤ w.re + ξ₀ + 1 :=
      ceil_le_add_one_of_le (by linarith)
    have h2 : ((n : ℕ) : ℝ) ≤ w.re + ξ₀ + 2 := by
      rw [hn]; push_cast; linarith
    linarith
  have hstrip : ‖u‖ ≤ |u.im| + ξ₀ + 3 := by
    have h1 : ‖u‖ ≤ |u.re| + |u.im| := by
      simpa using Complex.norm_le_abs_re_add_abs_im u
    have h2 : |u.re| ≤ ξ₀ + 2 := by
      rw [abs_le]; constructor <;> linarith
    linarith
  have huQ : u ∈ MandelDim.QLeft ξ₀ :=
    Work.Parab.halfplane_subset_QLeft ξ₀ (by show u.re < -ξ₀; linarith)
  have himu : |u.im| = |w.im| := by simp [hu]
  set ζ : ℂ := τ u with hζ
  have hbig' : 2 * (1 / ρ) + c * (1 + Real.log (2 + ‖ζ‖)) ≤ |ζ.im| :=
    hbig u huQ (by rw [himu]; exact le_of_lt hw) hstrip
  have hy := horbit ζ hbig'
  set y : ℕ → ℂ := fun j => (Work.FatouCoord.wMap f)^[j] ζ with hydef
  have hynorm : ∀ j : ℕ, 2 * (1 / ρ) ≤ ‖y j‖ := fun j => (hy j).1
  have hyre : ∀ j : ℕ, min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖))
      ≤ (y j).re := fun j => (hy j).2
  have hsmall : ∀ j : ℕ, ‖MandelDim.tau0 (y j)‖ < ρ := by
    intro j
    have h1 : 2 * (1 / ρ) ≤ ‖y j‖ := hynorm j
    have hpos : 0 < ‖y j‖ := lt_of_lt_of_le (by positivity) h1
    rw [norm_tau0, div_lt_iff₀ hpos]
    have h2 : ρ * (2 * (1 / ρ)) = 2 := by field_simp
    nlinarith [h1, h2]
  have hmem0 : ∀ j : ℕ, MandelDim.tau0 (y j) ∈ D₀ := by
    intro j
    refine hball ?_
    have h1 := hsmall j
    simpa [Metric.mem_ball, dist_eq_norm] using h1
  have hstep : ∀ x : ℂ, f (MandelDim.tau0 x) = MandelDim.tau0 (Work.FatouCoord.wMap f x) :=
    fun x => (tau0_wMap f x).symm
  have hiter : ∀ j : ℕ, f^[j] (seed τ u) = MandelDim.tau0 (y j) := by
    intro j
    induction j with
    | zero => simp [seed, hydef, hζ]
    | succ i ih =>
        rw [Function.iterate_succ_apply', ih]
        have h1 : y (i + 1) = Work.FatouCoord.wMap f (y i) := by
          simp only [hydef, Function.iterate_succ_apply']
        rw [h1, hstep]
  have hgood : Good f D₀ τ ξ₀ w := by
    refine ⟨n, ?_, ?_⟩
    · rw [← hu]; exact huQ
    · intro j hj
      rw [← hu, hiter j]
      exact hmem0 j
  have hcoord : coord f D₀ τ ξ₀ w = MandelDim.tau0 (y n) := by
    have h := coord_eq_of_witness (n := n) hs hgood (by rw [← hu]; exact huQ) (fun j hj => by
      rw [← hu, hiter j]
      exact hmem0 j)
    rwa [← hu, hiter n] at h
  have hζpos : 0 < ‖ζ‖ := by
    have h1 : 2 * (1 / ρ) ≤ ‖y 0‖ := hynorm 0
    have h2 : y 0 = ζ := by simp [hydef]
    rw [h2] at h1
    have : 0 < 2 * (1 / ρ) := by positivity
    linarith
  obtain ⟨N, hN⟩ := exists_iterate_re_gt (D := ‖ζ‖) c (min ζ.re 0) Mp hc hζpos
  set J : ℕ := max N n with hJ
  have hJN : N ≤ J := le_max_left _ _
  have hnJ : n ≤ J := le_max_right _ _
  have hJre : Mp < (y J).re := lt_of_lt_of_le (hN J hJN) (hyre J)
  have hJnorm : 1 / ρ < ‖y J‖ := by
    have h1 : 2 * (1 / ρ) ≤ ‖y J‖ := hynorm J
    have h2 : 1 / ρ < 2 * (1 / ρ) := by
      have : 0 < 1 / ρ := by positivity
      linarith
    linarith
  have hvalJ : ∀ j : ℕ, f^[j] (coord f D₀ τ ξ₀ w) = MandelDim.tau0 (y (n + j)) := by
    intro j
    induction j with
    | zero => rw [hcoord]; simp
    | succ i ih =>
        rw [Function.iterate_succ_apply', ih]
        have h1 : y (n + (i + 1)) = Work.FatouCoord.wMap f (y (n + i)) := by
          simp only [hydef]
          have h2 : n + (i + 1) = (n + i) + 1 := by omega
          rw [h2, Function.iterate_succ_apply']
        rw [h1, hstep]
  have hmemJ : ∀ j : ℕ, j ≤ J → f^[j] (coord f D₀ τ ξ₀ w) ∈ D₀ := by
    intro j hj
    rw [hvalJ j]
    exact hmem0 (n + j)
  have hab : ∀ j : ℕ, j < J - n → j ≤ J := fun j hj => le_trans (le_of_lt hj) (Nat.sub_le _ _)
  have hgoodJ : Good f D₀ τ ξ₀ (w + ((J - n : ℕ) : ℂ)) :=
    (good_add_of_iterate hs hgood (K := J - n) (fun j hj => hmemJ j (hab j hj))).1
  have hcoordJ : coord f D₀ τ ξ₀ (w + ((J - n : ℕ) : ℂ)) = MandelDim.tau0 (y J) := by
    have hbase : w + ((J - n : ℕ) : ℂ) - (J : ℂ) = u := by
      rw [hu, Nat.cast_sub hnJ]; ring
    have h := coord_eq_of_witness (n := J) hs hgoodJ (by rw [hbase]; exact huQ) (fun j hj => by
      rw [hbase, hiter j]
      exact hmem0 j)
    rwa [hbase, hiter J] at h
  have hpetal : coord f D₀ τ ξ₀ (w + ((J - n : ℕ) : ℂ)) ∈ Work.FatouCoord.Petal ρ Mp := by
    rw [hcoordJ]
    have hchart : Work.FatouCoord.chart (MandelDim.tau0 (y J)) = y J := by
      have h : MandelDim.tau0 = Work.FatouCoord.chart := rfl
      rw [← h]
      exact tau0_tau0 (y J)
    have hz0 : MandelDim.tau0 (y J) ≠ 0 := by
      intro h0
      have h1 : Work.FatouCoord.chart (MandelDim.tau0 (y J)) = 0 := by rw [h0]; simp
      rw [hchart] at h1
      have h2 : (0:ℝ) < ‖y J‖ := lt_trans (by positivity : (0:ℝ) < 1 / ρ) hJnorm
      rw [h1] at h2
      simp at h2
    rw [Work.FatouCoord.chart_mem_Petal_iff hρ hz0, Work.FatouCoord.mem_PetalChart]
    exact ⟨by rw [hchart]; exact hJre, by rw [hchart]; exact hJnorm⟩
  refine ⟨hgood, ?_⟩
  have hbasin : coord f D₀ τ ξ₀ (w + ((J - n : ℕ) : ℂ)) ∈ MandelDim.ParabolicBasin f D₀ :=
    hpetalbasin hpetal
  have hK' : f^[J - n] (coord f D₀ τ ξ₀ w)
      = coord f D₀ τ ξ₀ (w + ((J - n : ℕ) : ℂ)) :=
    (good_add_of_iterate hs hgood (K := J - n) (fun j hj => hmemJ j (hab j hj))).2.symm
  exact mem_basin_of_iterate hDopen hfD hbasin hK'
    (fun j hj => hmemJ j (le_trans hj (Nat.sub_le _ _)))


/-- For `|Im w|` large the point `w` lies in the maximal domain, and its coordinate lies in the
parabolic basin.  For `Re w ≥ -ξ₀ - 1` this is `ends_strip`; for `Re w < -ξ₀ - 1` one translates
`w` to the right until its real part reaches `[-ξ₀-1, -ξ₀)`, where every point of the run lies in
the sector `QLeft ξ₀`, so that the values are given by `hseedD`; `mem_basin_of_iterate` then
carries the basin back to `w`. -/
theorem ends_of_orbit {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ ρ Mp c η : ℝ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀) (hξ₀ : 0 < ξ₀) (hρ : 0 < ρ) (hMp : 0 < Mp) (hη : 0 < η)
    (hc : 0 ≤ c)
    (hball : Metric.ball 0 ρ ⊆ D₀)
    (hpetalbasin : Work.FatouCoord.Petal ρ Mp ⊆ MandelDim.ParabolicBasin f D₀)
    (hseedD : ∀ u ∈ MandelDim.QLeft ξ₀, seed τ u ∈ D₀)
    (hbig : ∀ u ∈ MandelDim.QLeft ξ₀, η ≤ |u.im| → ‖u‖ ≤ |u.im| + ξ₀ + 3 →
      2 * (1 / ρ) + c * (1 + Real.log (2 + ‖τ u‖)) ≤ |(τ u).im|)
    (horbit : ∀ ζ : ℂ, 2 * (1 / ρ) + c * (1 + Real.log (2 + ‖ζ‖)) ≤ |ζ.im| → ∀ j : ℕ,
      2 * (1 / ρ) ≤ ‖(Work.FatouCoord.wMap f)^[j] ζ‖ ∧
      ((Work.FatouCoord.wMap f)^[j] ζ).re ≥
        min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)))
    (hDopen : IsOpen D₀) (hfD : DifferentiableOn ℂ f D₀) :
    ∀ w : ℂ, η < |w.im| → w ∈ Dφ f D₀ τ ξ₀ ∧
      coord f D₀ τ ξ₀ w ∈ MandelDim.ParabolicBasin f D₀ := by
  intro w hw
  by_cases hcase : -ξ₀ - 1 ≤ w.re
  · exact ends_strip hs hξ₀ hρ hMp hη hc hball hpetalbasin hbig horbit hDopen hfD w hw hcase
  · rw [not_le] at hcase
    -- translate `w` to the right, into the strip
    set K : ℕ := Nat.floor (-ξ₀ - w.re) with hK
    have hx1 : 1 < -ξ₀ - w.re := by linarith
    have hKle : ((K : ℕ) : ℝ) ≤ -ξ₀ - w.re := Nat.floor_le (by linarith)
    have hKgt : -ξ₀ - w.re < ((K : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have hreK : -ξ₀ - 1 ≤ (w + (K : ℂ)).re := by
      have h1 : (w + (K : ℂ)).re = w.re + (K : ℝ) := by simp
      rw [h1]; linarith
    have hreKle : (w + (K : ℂ)).re ≤ -ξ₀ := by
      have h1 : (w + (K : ℂ)).re = w.re + (K : ℝ) := by simp
      rw [h1]; linarith
    have hQj : ∀ j : ℕ, j ≤ K → w + (j : ℂ) ∈ MandelDim.QLeft ξ₀ := by
      intro j hj
      have him : (w + (j : ℂ) + (ξ₀ : ℂ)).im = w.im := by simp
      have hne : w + (j : ℂ) + (ξ₀ : ℂ) ≠ 0 := by
        intro h0
        have h1 : (w + (j : ℂ) + (ξ₀ : ℂ)).im = 0 := by rw [h0]; simp
        rw [him] at h1
        have : (0 : ℝ) < |w.im| := lt_of_lt_of_le hη (le_of_lt hw)
        rw [h1] at this; simp at this
      refine mem_QLeft_of_re_le ?_ hne
      have h1 : (w + (j : ℂ)).re = w.re + (j : ℝ) := by simp
      have h4 : w.re + ((K : ℕ) : ℝ) = (w + (K : ℂ)).re := by simp
      have h2 : w.re + (j : ℝ) ≤ (w + (K : ℂ)).re := by
        have h3 : (j : ℝ) ≤ (K : ℝ) := by exact_mod_cast hj
        linarith
      rw [h1]
      exact le_trans h2 hreKle
    -- the chain of coordinates along the translate
    have hchain : ∀ j : ℕ, j ≤ K →
        Good f D₀ τ ξ₀ (w + (j : ℂ)) ∧
        coord f D₀ τ ξ₀ (w + (j : ℂ)) = f^[j] (coord f D₀ τ ξ₀ w) := by
      intro j hj
      induction j with
      | zero =>
          have hQ0 : w + ((0 : ℕ) : ℂ) ∈ MandelDim.QLeft ξ₀ := hQj 0 (Nat.zero_le K)
          refine ⟨Q_sub_Dφ f D₀ τ ξ₀ hQ0, by simp⟩
      | succ i ih =>
          have hi : i ≤ K := by omega
          obtain ⟨hgi, hci⟩ := ih hi
          have hQi : w + (i : ℂ) ∈ MandelDim.QLeft ξ₀ := hQj i hi
          have hcoord := coord_eq_of_witness hs hgi (n := 0) (by simpa using hQi)
            (by intro l hl; omega)
          have hmem : coord f D₀ τ ξ₀ (w + (i : ℂ)) ∈ D₀ := by
            rw [hcoord]; exact hseedD _ (by simpa using hQi)
          have hidx : w + ((i + 1 : ℕ) : ℂ) = (w + (i : ℂ)) + 1 := by push_cast; ring
          refine ⟨?_, ?_⟩
          · rw [hidx]; exact good_succ hgi hmem
          · rw [hidx, coord_succ hs hgi hmem, hci, Function.iterate_succ_apply']
    have hKval : coord f D₀ τ ξ₀ (w + (K : ℂ)) = f^[K] (coord f D₀ τ ξ₀ w) :=
      (hchain K le_rfl).2
    obtain ⟨-, hKbasin⟩ := ends_strip hs hξ₀ hρ hMp hη hc hball hpetalbasin hbig horbit hDopen hfD
      (w + (K : ℂ)) (by simpa using hw) hreK
    have hmid : ∀ j : ℕ, j ≤ K → f^[j] (coord f D₀ τ ξ₀ w) ∈ D₀ := by
      intro j hj
      have hQi : w + (j : ℂ) ∈ MandelDim.QLeft ξ₀ := hQj j hj
      have hcoord := coord_eq_of_witness hs (hchain j hj).1 (n := 0) (by simpa using hQi)
        (by intro l hl; omega)
      rw [← (hchain j hj).2, hcoord]
      exact hseedD _ (by simpa using hQi)
    exact ⟨Q_sub_Dφ f D₀ τ ξ₀ (by simpa using hQj 0 (Nat.zero_le K)),
      mem_basin_of_iterate hDopen hfD hKbasin hKval.symm hmid⟩

/-- **The end asymptotic of `τ₀ ∘ φ`** (the field `φ_asymp_ends` of `CoordData`): for `|Im w|`
large, uniformly in `Re w`, the inverse coordinate `τ₀ (φ w)` is asymptotic to
`w + a log (-w) + b`.  For `Re w ≥ -ξ₀ - 1` this follows from the chart-run asymptotic
`hwr` applied to the witness `u = w - (⌈Re w + ξ₀⌉ + 1)`; for `Re w < -ξ₀ - 1` the point `w`
itself lies in the sector, so the assertion is the definition of the asymptotic of `τ`. -/
theorem coord_ends_asymp {f : ℂ → ℂ} {D₀ : Set ℂ} {Φ : ℂ → ℂ} {L : Set ℂ} {τ : ℂ → ℂ}
    {ξ₀ ρ Mp c η Nc Kc : ℝ} {a b : ℂ}
    (hs : SeedHyp f D₀ Φ L τ ξ₀) (hξ₀ : 0 < ξ₀) (hρ : 0 < ρ) (hMp : 0 < Mp) (hη : 0 < η)
    (hc : 0 ≤ c)
    (hNc : Nc < 2 / ρ)
    (hball : Metric.ball 0 ρ ⊆ D₀)
    (hpetalbasin : Work.FatouCoord.Petal ρ Mp ⊆ MandelDim.ParabolicBasin f D₀)
    (hbig : ∀ u ∈ MandelDim.QLeft ξ₀, η ≤ |u.im| → ‖u‖ ≤ |u.im| + ξ₀ + 3 →
      2 * (1 / ρ) + c * (1 + Real.log (2 + ‖τ u‖)) ≤ |(τ u).im|)
    (horbit : ∀ ζ : ℂ, 2 * (1 / ρ) + c * (1 + Real.log (2 + ‖ζ‖)) ≤ |ζ.im| → ∀ j : ℕ,
      2 * (1 / ρ) ≤ ‖(Work.FatouCoord.wMap f)^[j] ζ‖ ∧
      ((Work.FatouCoord.wMap f)^[j] ζ).re ≥
        min ζ.re 0 + (j : ℝ) / 2 - c * (1 + Real.log (2 + (j : ℝ) + ‖ζ‖)))
    (hτasym : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₀, R < ‖u‖ →
      ‖τ u - (u + a * Complex.log (-u) + b)‖ < ε)
    (hchart : ∀ x : ℂ, Nc < ‖x‖ →
      ‖Work.FatouCoord.wMap f x - (x + 1 + a / x)‖ ≤ Kc / ‖x‖ ^ 2)
    (hwr : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ₀, ∀ n : ℕ,
      R < |(u + (n : ℂ)).im| →
      (∀ j ≤ n, Nc < ‖(Work.FatouCoord.wMap f)^[j] (τ u)‖) →
      ‖(Work.FatouCoord.wMap f)^[n] (τ u)
        - (u + (n : ℂ) + a * Complex.log (-(u + (n : ℂ))) + b)‖ < ε)
    (hDopen : IsOpen D₀) (hfD : DifferentiableOn ℂ f D₀) :
    ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < |w.im| →
      ‖MandelDim.tau0 (coord f D₀ τ ξ₀ w) - (w + a * Complex.log (-w) + b)‖ < ε := by
  intro ε hε
  obtain ⟨R₁, hR₁⟩ := hwr ε hε
  obtain ⟨R₂, hR₂⟩ := hτasym ε hε
  refine ⟨max (max R₁ R₂) (max (η + 1) (max (ξ₀ + 1) 0)), fun w hw => ?_⟩
  have hwR₁ : R₁ < |w.im| :=
    lt_of_le_of_lt (le_trans (le_max_left R₁ R₂) (le_max_left (max R₁ R₂) _)) hw
  have hwR₂ : R₂ < |w.im| :=
    lt_of_le_of_lt (le_trans (le_max_right R₁ R₂) (le_max_left (max R₁ R₂) _)) hw
  have hwη : η < |w.im| := by
    have h1 : η ≤ max (max R₁ R₂) (max (η + 1) (max (ξ₀ + 1) 0)) := by
      refine le_trans ?_ (le_max_right (max R₁ R₂) (max (η + 1) (max (ξ₀ + 1) 0)))
      refine le_trans ?_ (le_max_left (η + 1) (max (ξ₀ + 1) 0))
      linarith
    exact lt_of_le_of_lt h1 hw
  by_cases hcase : -ξ₀ - 1 ≤ w.re
  · set n : ℕ := Nat.ceil (w.re + ξ₀) + 1 with hn
    set u : ℂ := w - (n : ℂ) with hu
    have hre : u.re ≤ -ξ₀ - 1 := by
      have h1 : w.re + ξ₀ + 1 ≤ ((n : ℕ) : ℝ) := by
        have h2 := Nat.le_ceil (w.re + ξ₀)
        rw [hn]; push_cast; linarith
      have h2 : u.re = w.re - ((n : ℕ) : ℝ) := by rw [hu]; simp
      linarith
    have hre_lo : -ξ₀ - 2 ≤ u.re := by
      have h3 : ((Nat.ceil (w.re + ξ₀) : ℕ) : ℝ) ≤ w.re + ξ₀ + 1 :=
        ceil_le_add_one_of_le (by linarith)
      have h2 : ((n : ℕ) : ℝ) ≤ w.re + ξ₀ + 2 := by rw [hn]; push_cast; linarith
      have h4 : u.re = w.re - ((n : ℕ) : ℝ) := by rw [hu]; simp
      linarith
    have hstrip : ‖u‖ ≤ |u.im| + ξ₀ + 3 := by
      have h1 : ‖u‖ ≤ |u.re| + |u.im| := by
        simpa using Complex.norm_le_abs_re_add_abs_im u
      have h2 : |u.re| ≤ ξ₀ + 2 := by rw [abs_le]; constructor <;> linarith
      linarith
    have huQ : u ∈ MandelDim.QLeft ξ₀ :=
      Work.Parab.halfplane_subset_QLeft ξ₀ (by show u.re < -ξ₀; linarith)
    have himu : |u.im| = |w.im| := by simp [hu]
    have hbig' : 2 * (1 / ρ) + c * (1 + Real.log (2 + ‖τ u‖)) ≤ |(τ u).im| :=
      hbig u huQ (by rw [himu]; exact le_of_lt hwη) (by rw [hu] at hstrip; exact hstrip)
    have hy := horbit (τ u) hbig'
    have hsmall : ∀ j : ℕ, ‖MandelDim.tau0 ((Work.FatouCoord.wMap f)^[j] (τ u))‖ < ρ := by
      intro j
      have h1 : 2 * (1 / ρ) ≤ ‖(Work.FatouCoord.wMap f)^[j] (τ u)‖ := (hy j).1
      have hpos : 0 < ‖(Work.FatouCoord.wMap f)^[j] (τ u)‖ := lt_of_lt_of_le (by positivity) h1
      rw [norm_tau0, div_lt_iff₀ hpos]
      have h2 : ρ * (2 * (1 / ρ)) = 2 := by field_simp
      nlinarith [h1, h2]
    have hmem0 : ∀ j : ℕ, MandelDim.tau0 ((Work.FatouCoord.wMap f)^[j] (τ u)) ∈ D₀ := by
      intro j
      refine hball ?_
      have h1 := hsmall j
      simpa [Metric.mem_ball, dist_eq_norm] using h1
    have hstep : ∀ x : ℂ, f (MandelDim.tau0 x) = MandelDim.tau0 (Work.FatouCoord.wMap f x) :=
      fun x => (tau0_wMap f x).symm
    have hiter : ∀ j : ℕ, f^[j] (seed τ u) = MandelDim.tau0 ((Work.FatouCoord.wMap f)^[j] (τ u)) := by
      intro j
      induction j with
      | zero => simp [seed, tau0_tau0]
      | succ i ih =>
          rw [Function.iterate_succ_apply', ih, hstep]
          simp only [Function.iterate_succ_apply']
    have hgood : Good f D₀ τ ξ₀ w := by
      refine ⟨n, ?_, ?_⟩
      · rw [← hu]; exact huQ
      · intro j hj
        rw [← hu, hiter j]
        exact hmem0 j
    have hcoord : coord f D₀ τ ξ₀ w = f^[n] (seed τ u) :=
      coord_eq_of_witness hs hgood (by rw [← hu]; exact huQ) (fun j hj => by
        rw [← hu, hiter j]; exact hmem0 j)
    have hval : MandelDim.tau0 (coord f D₀ τ ξ₀ w)
        = (Work.FatouCoord.wMap f)^[n] (τ u) := by
      rw [hcoord, show seed τ u = MandelDim.tau0 (τ u) from rfl, tau0_iterate]
    rw [hval]
    have huw : u + (n : ℂ) = w := by rw [hu]; ring
    have himu' : |(u + (n : ℂ)).im| = |w.im| := by rw [huw]
    rw [← huw]
    refine hR₁ u huQ n ?_ ?_
    · rw [himu']; exact hwR₁
    · intro j hj
      have h2 : 2 / ρ ≤ ‖(Work.FatouCoord.wMap f)^[j] (τ u)‖ := by
        rw [div_eq_mul_one_div]
        exact (hy j).1
      exact lt_of_lt_of_le hNc h2
  · rw [not_le] at hcase
    have hwQ : w ∈ MandelDim.QLeft ξ₀ :=
      Work.Parab.halfplane_subset_QLeft ξ₀ (lt_trans hcase (by linarith : -ξ₀ - 1 < -ξ₀))
    have hG : Good f D₀ τ ξ₀ w := Q_sub_Dφ f D₀ τ ξ₀ hwQ
    have hcoord : coord f D₀ τ ξ₀ w = seed τ w := by
      have h := coord_eq_of_witness hs hG (n := 0) (by simpa using hwQ)
        (by intro j hj; omega)
      simpa using h
    have hval : MandelDim.tau0 (coord f D₀ τ ξ₀ w) = τ w := by
      rw [hcoord]; simp [seed, tau0_tau0]
    rw [hval]
    exact hR₂ w hwQ (lt_of_lt_of_le hwR₂ (Complex.abs_im_le_norm w))


/-! ## 14. The target theorem -/

/-- **The main construction.**  Every parabolic germ on a bounded domain carries §4.1 data:
the ζ-plane left coordinate (`leftCoordData_strong`, which also provides its properness at
infinity), its inverse `τ` on a large sector (`inverse_asymptotic`), the maximal-domain recursion
of `coordData_of_seed` with the orbit bounds (`orbit_bound`) and the imaginary-part bound
(`hbig_of_asymp`), and the end asymptotics (`wMap_run_asymptotic`, `coord_ends_asymp`,
`ends_of_orbit`, `cover_data`). -/
theorem exists_CoordData {f : ℂ → ℂ} {D₀ : Set ℂ}
    (d : Work.Parab.LeftCoordData f D₀) (hg : MandelDim.IsParabolicGerm f D₀) :
    Nonempty (Work.Parab.CoordData f D₀) := by
  classical
  -- ## 0. the strengthened ζ-plane left coordinate of `f`
  obtain ⟨dg, h, ag, rg, Ag, Ag', hbP, haeq, hproper⟩ :=
    Work.Parab.coordData.leftCoordData_strong hg
  -- ## 1. the basin data of `f`
  obtain ⟨_Φb, _hp, _ap, rp, _Ap, _Ap', Mp, hbPp, hballP, hMP, hpetalbasin, _hmapsp, _hconvp,
    _hdiffp, _habelp, _hinjp, _hagreep⟩ :=
    Work.Parab.basinCoord.exists_basin_coordinate hg
  -- ## 2. the inverse of the left coordinate on a large sector
  obtain ⟨hτspec₁, hτdiff₁, hτasym₁⟩ :=
    Work.Parab.inversion.inverse_asymptotic_invOn (Φ := dg.Φ) (L := dg.L) (ξ := dg.ξ₁)
      (a := dg.a) (b := dg.b) dg.ξ₁_pos dg.L_open dg.Φ_holo dg.Φ_inj dg.Φ_asym hproper dg.Φ_img
  set τ : ℂ → ℂ := Work.Parab.inversion.invOn dg.Φ dg.L with hτdef
  -- ## 3. the second-order chart estimate
  obtain ⟨Rc, Kc, hRcpos, _hRcr, hKcnn, hchart0⟩ := Work.Parab.leftCoord.wMap_large_estimates hbP
  -- ## 4. the radius `ρ` (small enough that the chart threshold is below `2 / ρ`)
  set ρ : ℝ := min rp (1 / (Rc + 1)) with hρdef
  have hρpos : 0 < ρ := lt_min hbPp.hr (by positivity)
  have hρrp : ρ ≤ rp := min_le_left rp (1 / (Rc + 1))
  have hρle : ρ ≤ 1 / (Rc + 1) := min_le_right rp (1 / (Rc + 1))
  have hρNc : Rc < 2 / ρ := by
    rw [lt_div_iff₀ hρpos]
    have h1 : Rc * ρ ≤ Rc * (1 / (Rc + 1)) := mul_le_mul_of_nonneg_left hρle hRcpos.le
    have h2 : Rc * (1 / (Rc + 1)) < 1 := by
      rw [mul_one_div, div_lt_iff₀ (by linarith : (0:ℝ) < (Rc + 1))]
      linarith
    linarith
  -- ## 5. the seed facts on a large sector
  have hρspos : 0 < ρ / 2 := by linarith
  obtain ⟨ξ₀, hξ₁ξ₀, hξ₀pos, hseedfacts⟩ :=
    Work.Parab.coordData.tau_seed_gen (f := f) (h := h) (c := ag) (a := dg.a) (b := dg.b)
      hbP hρspos dg.M₀_pos dg.M₁_pos dg.ξ₁_pos dg.L_left dg.L_im hτasym₁
  -- ## 6. the final vertex `ξ` and the covering of the repelling cone
  set ξ : ℝ := max ξ₀ (3 * dg.ξ₁ + 1) with hξdef
  have hξ₀ξ : ξ₀ ≤ ξ := le_max_left ξ₀ (3 * dg.ξ₁ + 1)
  have h3ξ₁ξ : 3 * dg.ξ₁ + 1 ≤ ξ := le_max_right ξ₀ (3 * dg.ξ₁ + 1)
  have hξpos : 0 < ξ := lt_of_lt_of_le hξ₀pos hξ₀ξ
  have hξ₁ξ : dg.ξ₁ ≤ ξ := by linarith [h3ξ₁ξ, dg.ξ₁_pos]
  have hξξ₀ : MandelDim.QLeft ξ ⊆ MandelDim.QLeft ξ₀ := QLeft_anti hξ₀ξ
  have hξξ₁ : MandelDim.QLeft ξ ⊆ MandelDim.QLeft dg.ξ₁ := QLeft_anti hξ₁ξ
  obtain ⟨ρc, hρcpos, hcover0⟩ :=
    Work.Parab.coordData.cover_data_range (Φ := dg.Φ) (L := dg.L) (M₀ := dg.M₀) (M₁ := dg.M₁)
      (a := dg.a) (b := dg.b) dg.M₀_pos dg.M₁_pos dg.L_left dg.L_im dg.Φ_asym ξ
  have hnormξ : ∀ u ∈ MandelDim.QLeft ξ, dg.ξ₁ < ‖u‖ := by
    intro u hu
    have h1 : ξ / 3 < ‖u‖ := Work.Parab.QLeft_subset_norm hξpos hu
    have h2 : dg.ξ₁ < ξ / 3 := by linarith [h3ξ₁ξ]
    linarith
  -- ## 8. the seed data on `QLeft ξ`
  have hτbig : ∀ u ∈ MandelDim.QLeft ξ, 1 / ρ ≤ ‖τ u‖ := by
    intro u hu
    have h1 : 1 / (ρ / 2) ≤ ‖τ u‖ := (hseedfacts u (hξξ₀ hu)).1
    have h2 : 1 / ρ < 1 / (ρ / 2) := by
      refine one_div_lt_one_div_of_lt hρspos ?_
      linarith
    linarith
  have hτmem : ∀ u ∈ MandelDim.QLeft ξ, τ u ∈ dg.L :=
    fun u hu => (hseedfacts u (hξξ₀ hu)).2.1
  have hτwmap : ∀ u ∈ MandelDim.QLeft ξ, Work.FatouCoord.wMap f (τ u) ∈ dg.L :=
    fun u hu => (hseedfacts u (hξξ₀ hu)).2.2
  have hspecξ : ∀ u ∈ MandelDim.QLeft ξ, dg.Φ (τ u) = u :=
    fun u hu => hτspec₁ u (hnormξ u hu) (hξξ₁ hu)
  have hs : SeedHyp f D₀ dg.Φ dg.L τ ξ := ⟨hspecξ, hτmem, hτwmap, dg.Φ_inj, dg.Φ_abel⟩
  have hQW : MandelDim.QLeft ξ ⊆ {w : ℂ | w ∈ MandelDim.QLeft dg.ξ₁ ∧ dg.ξ₁ < ‖w‖} :=
    fun u hu => ⟨hξξ₁ hu, hnormξ u hu⟩
  have hseedD : ∀ u ∈ MandelDim.QLeft ξ, seed τ u ∈ D₀ := by
    intro u hu
    have h1 : 1 / (ρ / 2) ≤ ‖τ u‖ := (hseedfacts u (hξξ₀ hu)).1
    have hτu_pos : 0 < ‖τ u‖ := lt_of_lt_of_le (div_pos one_pos hρspos) h1
    have h2 : 1 / ‖τ u‖ ≤ ρ / 2 := by
      rw [div_le_iff₀ hτu_pos]
      rw [div_le_iff₀ hρspos] at h1
      linarith [h1, mul_comm (ρ / 2) ‖τ u‖]
    have h3 : 1 / ‖τ u‖ < rp := by linarith
    have hmem : seed τ u ∈ Metric.ball 0 rp := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      rw [show seed τ u = MandelDim.tau0 (τ u) from rfl, norm_tau0]
      exact h3
    exact hballP hmem
  have hballρ : Metric.ball 0 ρ ⊆ D₀ := fun z hz => hballP (Metric.ball_subset_ball hρrp hz)
  have hpetalρ : Work.FatouCoord.Petal ρ Mp ⊆ MandelDim.ParabolicBasin f D₀ :=
    fun z hz => hpetalbasin (Work.FatouCoord.Petal_mono hρrp le_rfl hz)
  -- ## 9. the orbit bound and the imaginary-part bound
  obtain ⟨c, hc, hcprop⟩ := Work.Parab.coordData.orbit_bound (f := f) (h := h) (a := ag)
    (r := rg) (A := Ag) (A' := Ag') hbP (1 / ρ) (div_pos one_pos hρpos)
  have hτasymξ : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ, R < ‖u‖ →
      ‖τ u - (u + dg.a * Complex.log (-u) + dg.b)‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := hτasym₁ ε hε
    exact ⟨R, fun u hu hRu => hR u (hξξ₁ hu) hRu⟩
  obtain ⟨ηb, _hηbpos, hηb⟩ := Work.Parab.coordData.hbig_of_asymp (τ := τ) (a := dg.a) (b := dg.b)
    (ξ₀ := ξ) (ρ := ρ) (c := c) hξpos hρpos hc hτasymξ
  set η : ℝ := max ηb 1 with hηdef
  have hηpos : 0 < η := lt_of_lt_of_le one_pos (le_max_right ηb 1)
  have hbig : ∀ u ∈ MandelDim.QLeft ξ, η ≤ |u.im| → ‖u‖ ≤ |u.im| + ξ + 3 →
      2 * (1 / ρ) + c * (1 + Real.log (2 + ‖τ u‖)) ≤ |(τ u).im| :=
    fun u hu h1 h2 => hηb u hu (le_trans (le_max_left ηb 1) h1) h2
  -- ## 10. the covering of the repelling cone
  have hcoord0 : ∀ {u : ℂ}, u ∈ MandelDim.QLeft ξ → coord f D₀ τ ξ u = seed τ u := by
    intro u hu
    have hG : Good f D₀ τ ξ u := ⟨0, by simpa using hu, by intro j hj; omega⟩
    have h := coord_eq_of_witness hs hG (n := 0) (by simpa using hu) (by intro j hj; omega)
    simpa using h
  have hcover : ∃ ρc' : ℝ, 0 < ρc' ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρc' →
      |z.arg| ≤ Real.pi / 2 + Real.pi / 12 →
        ∃ w ∈ MandelDim.QLeft ξ, coord f D₀ τ ξ w = z := by
    refine ⟨ρc, hρcpos, fun z hz0 hz hzarg => ?_⟩
    obtain ⟨hL, hQ⟩ := hcover0 z hz0 hz hzarg
    refine ⟨dg.Φ (MandelDim.tau0 z), hQ, ?_⟩
    have hτeq : τ (dg.Φ (MandelDim.tau0 z)) = MandelDim.tau0 z := by
      have hex : ∃ ζ ∈ dg.L, dg.Φ ζ = dg.Φ (MandelDim.tau0 z) :=
        ⟨MandelDim.tau0 z, hL, rfl⟩
      show Work.Parab.inversion.invOn dg.Φ dg.L (dg.Φ (MandelDim.tau0 z)) = MandelDim.tau0 z
      rw [Work.Parab.inversion.invOn_eq_of hex]
      exact dg.Φ_inj (Classical.choose_spec hex).1 hL (Classical.choose_spec hex).2
    have hcc : coord f D₀ τ ξ (dg.Φ (MandelDim.tau0 z)) = z := by
      rw [hcoord0 hQ]
      show MandelDim.tau0 (τ (dg.Φ (MandelDim.tau0 z))) = z
      rw [hτeq, tau0_tau0]
    exact hcc
  -- ## 11. the chart estimate with the exact coefficient
  have hchart : ∀ x : ℂ, Rc < ‖x‖ →
      ‖Work.FatouCoord.wMap f x - (x + 1 + dg.a / x)‖ ≤ Kc / ‖x‖ ^ 2 := by
    intro x hx
    have h1 := (hchart0 x hx).2.1
    rwa [← haeq] at h1
  -- ## 12. the chart-run asymptotic and the two end lemmas
  have hwr : ∀ ε > 0, ∃ R : ℝ, ∀ u ∈ MandelDim.QLeft ξ, ∀ n : ℕ,
      R < |(u + (n : ℂ)).im| →
      (∀ j ≤ n, Rc < ‖(Work.FatouCoord.wMap f)^[j] (τ u)‖) →
      ‖(Work.FatouCoord.wMap f)^[n] (τ u)
        - (u + (n : ℂ) + dg.a * Complex.log (-(u + (n : ℂ))) + dg.b)‖ < ε :=
    Work.Parab.coordData.wMap_run_asymptotic (f := f) (Φ := dg.Φ) (L := dg.L) (τ := τ)
      (ξ₀ := ξ) (a := dg.a) (b := dg.b) (K := Kc) (Nc := Rc)
      hξpos hRcpos hKcnn hchart hτmem hspecξ hτasymξ dg.Φ_asym hproper
  have hendasym : ∀ ε > 0, ∃ R : ℝ, ∀ w : ℂ, R < |w.im| →
      ‖MandelDim.tau0 (coord f D₀ τ ξ w) - (w + (1 - ag) * Complex.log (-w) + dg.b)‖ < ε := by
    intro ε hε
    obtain ⟨R, hR⟩ := coord_ends_asymp (f := f) (D₀ := D₀) (Φ := dg.Φ) (L := dg.L) (τ := τ)
      (ξ₀ := ξ) (ρ := ρ) (Mp := Mp) (c := c) (η := η) (Nc := Rc) (Kc := Kc)
      (a := dg.a) (b := dg.b) hs hξpos hρpos hMP hηpos hc hρNc hballρ hpetalρ hbig hcprop
      hτasymξ hchart hwr hg.1 hg.2.2.1 ε hε
    refine ⟨R, fun w hw => ?_⟩
    rw [← haeq]
    exact hR w hw
  have hends : ∀ w : ℂ, η < |w.im| → w ∈ Dφ f D₀ τ ξ ∧
      coord f D₀ τ ξ w ∈ MandelDim.ParabolicBasin f D₀ :=
    ends_of_orbit (f := f) (D₀ := D₀) (Φ := dg.Φ) (L := dg.L) (τ := τ) (ξ₀ := ξ)
      (ρ := ρ) (Mp := Mp) (c := c) (η := η) hs hξpos hρpos hMP hηpos hc hballρ hpetalρ
      hseedD hbig hcprop hg.1 hg.2.2.1
  -- ## 13. the assembly
  exact coordData_of_seed (f := f) (D₀ := D₀) (Φ := dg.Φ) (L := dg.L) (τ := τ)
    (W := {w : ℂ | w ∈ MandelDim.QLeft dg.ξ₁ ∧ dg.ξ₁ < ‖w‖}) (ξ₀ := ξ) (ρ := ρ) (η₀ := η)
    (a := dg.a) (b := dg.b) hs hξpos hρpos hηpos hballρ hg.1 hg.2.2.1
    ((isOpen_QLeft dg.ξ₁).inter (isOpen_lt continuous_const continuous_norm)) hτdiff₁ hQW
    hτbig hseedD hτasymξ dg.Φ_asym h ag rg Ag Ag' hbP haeq hendasym hcover hends

end
end Work.Parab.coordData

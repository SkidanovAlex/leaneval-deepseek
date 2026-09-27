import Mathlib
import Submission.Work.EKLC6Core.cutSetup
import Submission.Work.EKLC6Core.cut_defs
import Submission.Work.EKLC6Core.cut_cells
import Submission.Work.EKLC6Core.inj_region_measure
import Submission.Work.EKLC6Core.thin_boundary_partition
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.inv_mem_V
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLNonExc.DinjFacts

/-!
# `Work.EKLC6Core.cutData_of_partition`

From a partition of `X₃` into open cells `Q i` of `V ρ`-diameter with `µ`-thin boundaries and
centres `mkX (g i)` whose stabiliser is injective at scale `30 ρ`, build the `CutData` of the
"cut" construction (Pisa 7.38) at *some* scale `≤ ρ`.

## The construction

The cells of the `CutData` are **not** the given cells: the uniqueness of the lift required by
`CutData.lift_uniq` on the ball `(V (10 S.ρ)) · (g i)` is a property of the scale, and the given
cells only guarantee injectivity of the stabiliser at scale `30 ρ`.  Instead:

* `ε - µ ((⋃ Q)ᶜ) > 0` is the "room" left over by the given partition; the leftover is absorbed
  into the `CutData`'s open piece `bad`.
* `η` is chosen so that the set of points whose stabiliser contains a nontrivial conjugate of
  `Γ₃` inside `V η` has measure `room/4` (`inj_region_measure`); `δ` so that
  `Wset δ ⊆ V η`, whence `(Dinj δ)ᶜ` has measure `< room/4` (`Dinj δ` = the points at which the
  `V δ`-action is injective).
* A thin-boundary partition of `X₃` at a *much smaller* scale `r` (`thin_boundary_partition`) is
  taken; its pieces of positive `µ`-measure have non-empty interior, and the pieces meeting
  `Dinj δ` are kept as cells; the remaining ones are absorbed into `bad`.  The total measure of
  the discarded pieces is `< room/4` because they are disjoint subsets of `(Dinj δ)ᶜ`.
* `S.ρ := t / 10` with `t := 14 r`: the `V`-arithmetic lemmas at the top give that each piece
  lies in the `V t`-ball of its reference point, and the injectivity of the `V δ`-action keeps
  the lift unique in that ball.

The given cells `Q i`, their thin boundaries and the hyothesis `hinj` are only used to produce
the room `ε - µ ((⋃ Q)ᶜ) > 0` (and the positivity of `ρ`); the *construction* only needs the
"room" and `µ`.
-/

namespace Work.EKLC6Core
open MeasureTheory Topology Filter Set
open scoped ENNReal Pointwise
open Work.EKLContract

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

/-- `a * b ∈ V (5s)` for `a, b ∈ V s`, `s ≤ 1`. -/
private lemma V_mul_aux {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) {a b : SL3}
    (ha : a ∈ V s) (hb : b ∈ V s) : a * b ∈ V (5 * s) := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have h := Work.EKLRelCross.entries_mul_sub_one_le
    (A := (a : Matrix (Fin 3) (Fin 3) ℝ)) (B := (b : Matrix (Fin 3) (Fin 3) ℝ)) i j
    (fun k l => by simpa using ha k l) (fun k l => by simpa using hb k l)
    (le_of_lt hs) (le_of_lt hs)
  have harith : s + s + 3 * s * s ≤ 5 * s := by nlinarith [hs, hs1]
  exact lt_of_lt_of_le h harith

/-- `a * b⁻¹ ∈ V (14s)` for `a, b ∈ V s`, `s ≤ 1/10`. -/
private lemma V_mul_inv_aux {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/10) {a b : SL3}
    (ha : a ∈ V s) (hb : b ∈ V s) : a * b⁻¹ ∈ V (14 * s) := by
  have hbinv : b⁻¹ ∈ V (10 * s) := Work.EKLComp.inv_mem_V hs (by linarith) hb
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have h := Work.EKLRelCross.entries_mul_sub_one_le
    (A := (a : Matrix (Fin 3) (Fin 3) ℝ)) (B := ((b⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j
    (fun k l => by simpa using ha k l) (fun k l => by simpa using hbinv k l)
    (le_of_lt hs) (by linarith)
  have harith : s + 10 * s + 3 * s * (10 * s) ≤ 14 * s := by nlinarith [hs, hs1]
  exact lt_of_lt_of_le h harith

/-- `a⁻¹ * b ∈ V (14s)` for `a, b ∈ V s`, `s ≤ 1/10`. -/
private lemma V_inv_mul_aux {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1/10) {a b : SL3}
    (ha : a ∈ V s) (hb : b ∈ V s) : a⁻¹ * b ∈ V (14 * s) := by
  have hainv : a⁻¹ ∈ V (10 * s) := Work.EKLComp.inv_mem_V hs (by linarith) ha
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  have h := Work.EKLRelCross.entries_mul_sub_one_le
    (A := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) (B := (b : Matrix (Fin 3) (Fin 3) ℝ)) i j
    (fun k l => by simpa using hainv k l) (fun k l => by simpa using hb k l)
    (by linarith) (le_of_lt hs)
  have harith : 10 * s + s + 3 * (10 * s) * s ≤ 14 * s := by nlinarith [hs, hs1]
  exact lt_of_lt_of_le h harith

/-- The complement of `Dinj δ` is contained in the "bad region" of radius `η` if
`Wset δ ⊆ V η`. -/
private lemma compl_Dinj_subset_badRegion {δ η : ℝ}
    (h : Work.EKLNonExc.DinjAux.Wset δ ⊆ V η) :
    (Work.EKLNonExc.Dinj δ)ᶜ ⊆ mkX '' {g : SL3 | ∃ γ ∈ Γ3, γ ≠ 1 ∧ g * γ * g⁻¹ ∈ V η} := by
  rw [Work.EKLNonExc.DinjAux.complDinj]
  rintro x ⟨k, hk, rfl⟩
  rw [Work.EKLNonExc.DinjAux.mem_Lbad] at hk
  obtain ⟨γ, hγne, hγW⟩ := hk
  refine ⟨k, ?_, rfl⟩
  exact ⟨(γ : SL3), γ.2, fun h1 => hγne (Subtype.ext h1), h hγW⟩

theorem cutData_of_partition {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {N : ℕ} (Q : Fin N → Set Work.EKLContract.X3) (g : Fin N → Work.EKLContract.SL3)
    (c ρ : ℝ) (hρ : 0 < ρ) (hc : 0 < c)
    (hopen : ∀ i, IsOpen (Q i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
    (hgm : ∀ i, Work.EKLContract.mkX (g i) ∈ Q i)
    (hsub : ∀ i, Q i ⊆ (fun u : Work.EKLContract.SL3 => u • Work.EKLContract.mkX (g i)) ''
        (Work.EKLContract.V ρ))
    (hinj : ∀ i (γ : Work.EKLContract.SL3), γ ∈ Work.EKLContract.Γ3 →
        g i * γ * (g i)⁻¹ ∈ Work.EKLContract.V (30 * ρ) → γ = 1)
    (hthin : ∀ η : ℝ, 0 < η →
        μ (⋃ i, Work.EKLC6Core.VThick η (frontier (Q i))) ≤ ENNReal.ofReal (c * η))
    (hmeas : ∀ i, MeasurableSet (Q i))
    (ε : ℝ) (hε : 0 < ε) (hbad : μ ((⋃ i, Q i))ᶜ < ENNReal.ofReal ε) :
    ∃ S : Work.EKLC6Core.CutData μ U ε, S.ρ ≤ ρ := by
  classical
  haveI : IsFiniteMeasure μ := inferInstance
  -- ## Step 0: the room left over by the given partition
  have hμne : μ ((⋃ i, Q i))ᶜ ≠ ⊤ := measure_ne_top μ _
  have hroom_lt : (μ ((⋃ i, Q i))ᶜ).toReal < ε :=
    (ENNReal.lt_ofReal_iff_toReal_lt hμne).mp hbad
  set room : ℝ := ε - (μ ((⋃ i, Q i))ᶜ).toReal with hroomdef
  have hroom_pos : 0 < room := by
    have h0 : (0:ℝ) ≤ (μ ((⋃ i, Q i))ᶜ).toReal := ENNReal.toReal_nonneg
    rw [hroomdef]; linarith
  have hroom_le : room ≤ ε := by
    have h0 : (0:ℝ) ≤ (μ ((⋃ i, Q i))ᶜ).toReal := ENNReal.toReal_nonneg
    rw [hroomdef]; linarith
  -- ## Step 1: a small set of points with poor stabiliser
  obtain ⟨η, hηpos, hηsmall⟩ :=
    Work.EKLC6Core.inj_region_measure (μ := μ) (room / 4) (by linarith)
  -- ## Step 2: a radius δ with `(Dinj δ)ᶜ` inside it
  have hVηnhds : V η ∈ 𝓝 (1 : SL3) := by
    obtain ⟨ho, h1⟩ := Work.EKLContract.Lemmas.V_open_one η hηpos
    exact ho.mem_nhds h1
  obtain ⟨δ, hδpos, hδW⟩ := Work.EKLNonExc.exists_Wset_subset hVηnhds
  have hδsmall : μ ((Work.EKLNonExc.Dinj δ)ᶜ) < ENNReal.ofReal (room / 4) :=
    lt_of_le_of_lt (measure_mono (compl_Dinj_subset_badRegion hδW)) hηsmall
  -- ## Step 3: the scales
  set r : ℝ := min (min (δ / 2000) (ρ / 1000)) (1 / 1000) with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact lt_min (lt_min (by linarith) (by linarith)) (by norm_num)
  have hrδ : r ≤ δ / 2000 := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrρ : r ≤ ρ / 1000 := by
    rw [hrdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hr10 : r ≤ 1 / 10 := by
    rw [hrdef]; exact le_trans (min_le_right _ _) (by norm_num)
  have hr1 : r ≤ 1 / 1000 := by
    rw [hrdef]; exact min_le_right _ _
  have h980 : 980 * r ≤ δ := by linarith [hrδ, hδpos]
  have h196 : 196 * r ≤ δ := by linarith [hrδ, hδpos]
  set t : ℝ := 14 * r with htdef
  have htpos : 0 < t := by rw [htdef]; linarith
  have ht10 : t ≤ 1 / 10 := by rw [htdef]; linarith [hr1]
  have ht1 : t ≤ 1 := by linarith
  have h5t10 : 5 * t ≤ 1 / 10 := by rw [htdef]; linarith [hr1]
  have h70 : 14 * (5 * t) ≤ δ := by rw [htdef] at *; linarith [h980]
  have hρ10 : (10 : ℝ) * (t / 10) = t := by ring
  -- ## Step 4: the thin-boundary partition at scale `r`
  obtain ⟨Np, P, i₀, cp, hcp, hPmeas, hPdisj, hPcov, hPsub, hPi₀, hPthin⟩ :=
    Work.EKLC6Core.thin_boundary_partition μ (room / 2) r (by linarith) hrpos
  have hfront0 : μ (⋃ i, frontier (P i)) = 0 :=
    Work.EKLC6Core.measure_iUnion_frontier_eq_zero P hcp
      (fun η hη => by simpa only [VThick_def] using hPthin η hη)
  have hfront_single : ∀ i, μ (frontier (P i)) = 0 := fun i =>
    measure_mono_null (Set.subset_iUnion (fun i => frontier (P i)) i) hfront0
  -- ## Step 5: the good pieces and the reindexing
  let Good : Set (Fin Np) := {i | i ≠ i₀ ∧ ((interior (P i)) ∩ Work.EKLNonExc.Dinj δ).Nonempty}
  have hGoodFin : Good.Finite := Set.toFinite Good
  letI : Fintype ↥Good := hGoodFin.fintype
  let m : ℕ := Fintype.card ↥Good
  let ee : ↥Good ≃ Fin m := Fintype.equivFin ↥Good
  let idx : Fin m → Fin Np := fun j => (ee.symm j : ↥Good).1
  have hidxGood : ∀ j, idx j ∈ Good := fun j => (ee.symm j : ↥Good).2
  have hidxne : ∀ j, idx j ≠ i₀ := fun j => (hidxGood j).1
  have hidxint : ∀ j, ((interior (P (idx j))) ∩ Work.EKLNonExc.Dinj δ).Nonempty :=
    fun j => (hidxGood j).2
  have hidxinj : Function.Injective idx := by
    intro j k hjk
    have h1 : (ee.symm j : ↥Good) = ee.symm k := Subtype.ext hjk
    exact ee.symm.injective h1
  let yv : Fin m → X3 := fun j => Classical.choose (hidxint j)
  have hyv : ∀ j, yv j ∈ interior (P (idx j)) ∧ yv j ∈ Work.EKLNonExc.Dinj δ := fun j =>
    Classical.choose_spec (hidxint j)
  let gg : Fin m → SL3 := fun j => Classical.choose (QuotientGroup.mk_surjective (yv j))
  have hgg : ∀ j, mkX (gg j) = yv j := fun j =>
    Classical.choose_spec (QuotientGroup.mk_surjective (yv j))
  let cell : Fin m → Set X3 := fun j => interior (P (idx j))
  have hcent : ∀ j, ∃ x : X3, P (idx j) ⊆ (fun u : SL3 => u • x) '' V r := fun j =>
    hPsub (idx j) (hidxne j)
  let xc : Fin m → X3 := fun j => Classical.choose (hcent j)
  have hxc : ∀ j, P (idx j) ⊆ (fun u : SL3 => u • xc j) '' V r := fun j =>
    Classical.choose_spec (hcent j)
  -- ## Step 6: each cell lies in the `V t`-ball of its reference point
  have hcell_ball : ∀ j, cell j ⊆ (fun u : SL3 => u • yv j) '' V t := by
    intro j z hz
    obtain ⟨u, hu, rfl⟩ := hxc j (interior_subset hz)
    obtain ⟨v, hv, hvy⟩ := hxc j (interior_subset (hyv j).1)
    have hxv : xc j = v⁻¹ • yv j := by
      have h1 : v • xc j = yv j := hvy
      rw [← h1, inv_smul_smul]
    refine ⟨u * v⁻¹, ?_, ?_⟩
    · show u * v⁻¹ ∈ V (14 * r)
      exact V_mul_inv_aux hrpos hr10 hu hv
    · show (u * v⁻¹) • yv j = u • xc j
      rw [mul_smul, ← hxv]
  -- ## Step 7: injectivity of the `V s`-action at the reference points
  have hinj_y : ∀ j (s : ℝ), 0 < s → s ≤ 1 / 10 → 14 * s ≤ δ →
      ∀ u v : SL3, u ∈ V s → v ∈ V s → u • yv j = v • yv j → u = v := by
    intro j s hspos hs10 hsδ u v hu hv huv
    have hwu : v⁻¹ * u ∈ V (14 * s) := V_inv_mul_aux hspos hs10 hv hu
    have hwδ : v⁻¹ * u ∈ V δ := fun a b => lt_of_lt_of_le (hwu a b) hsδ
    have hfix : (v⁻¹ * u) • yv j = yv j := by
      rw [mul_smul, huv, inv_smul_smul]
    have h1δ : (1 : SL3) ∈ V δ := (Work.EKLContract.Lemmas.V_open_one δ hδpos).2
    have hres : v⁻¹ * u = 1 :=
      (Work.EKLNonExc.mem_Dinj.mp (hyv j).2) (v⁻¹ * u) 1 hwδ h1δ
        (by rw [hfix, one_smul])
    exact (inv_mul_eq_one.mp hres).symm
  -- ## Step 8: the lift
  let liftF : Fin m → X3 → SL3 := fun j z =>
    if h : z ∈ cell j then Classical.choose (hcell_ball j h) * gg j else 1
  have hliftF_mem : ∀ j z (hz : z ∈ cell j),
      liftF j z = Classical.choose (hcell_ball j hz) * gg j := by
    intro j z hz; simp only [liftF, dif_pos hz]
  have hliftF_spec : ∀ j z (hz : z ∈ cell j),
      Classical.choose (hcell_ball j hz) ∈ V t ∧
        Classical.choose (hcell_ball j hz) • yv j = z := fun j z hz =>
    Classical.choose_spec (hcell_ball j hz)
  -- ## Step 9: the bad set and the measure bookkeeping
  have VThick_iUnion : ∀ (η : ℝ) (f : Fin m → Set X3),
      VThick η (⋃ j, f j) = ⋃ j, VThick η (f j) := by
    intro η f
    ext z
    constructor
    · intro hz
      obtain ⟨x, hx, g, hg, hgx⟩ := mem_VThick.mp hz
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hx
      exact Set.mem_iUnion.mpr ⟨j, mem_VThick.mpr ⟨x, hxj, g, hg, hgx⟩⟩
    · intro hz
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz
      obtain ⟨x, hx, g, hg, hgx⟩ := mem_VThick.mp hzj
      exact mem_VThick.mpr ⟨x, Set.mem_iUnion.mpr ⟨j, hx⟩, g, hg, hgx⟩
  let bad : Set X3 := interior ((⋃ j, cell j))ᶜ
  have hcell_eq : (⋃ j, cell j) = ⋃ i ∈ (Good : Set (Fin Np)), interior (P i) := by
    ext z
    constructor
    · intro hz
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion₂.mpr ⟨idx j, hidxGood j, hzj⟩
    · intro hz
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
      obtain ⟨j, hj⟩ := ee.symm.surjective ⟨i, hi⟩
      have hidx : idx j = i := congrArg Subtype.val hj
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      show z ∈ interior (P (idx j))
      rw [hidx]; exact hzi
  have hdecomp : ((⋃ i ∈ (Good : Set (Fin Np)), interior (P i)))ᶜ
      ⊆ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i) ∪ (⋃ i, P i \ interior (P i)) := by
    intro z hz
    have hzu : z ∉ ⋃ i ∈ (Good : Set (Fin Np)), interior (P i) := hz
    have hzuniv : z ∈ ⋃ i, P i := by rw [hPcov]; exact Set.mem_univ z
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hzuniv
    by_cases hG : i ∈ Good
    · refine Or.inr (Set.mem_iUnion.mpr ⟨i, ?_⟩)
      exact ⟨hi, fun hint => hzu (Set.mem_iUnion₂.mpr ⟨i, hG, hint⟩)⟩
    · exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, by simpa using hG, hi⟩)
  have hint_zero : ∀ i, μ (P i \ interior (P i)) = 0 := fun i =>
    measure_mono_null (fun z hz => by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hz.1, by
        rw [closure_compl]
        exact fun h2 => hz.2 h2⟩)
      (hfront_single i)
  have hunion_int_zero : μ (⋃ i, P i \ interior (P i)) = 0 := by
    rw [measure_iUnion_null_iff]; exact hint_zero
  have hIntBad : ∀ i, i ∉ Good → i ≠ i₀ → interior (P i) ⊆ (Work.EKLNonExc.Dinj δ)ᶜ := by
    intro i hi hi0 z hz hzD
    exact hi ⟨hi0, ⟨z, hz, hzD⟩⟩
  have hIntBound : μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i))
      ≤ ENNReal.ofReal (room / 2) + ENNReal.ofReal (room / 4) := by
    have hsub : (⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i))
        ⊆ P i₀ ∪ (Work.EKLNonExc.Dinj δ)ᶜ := by
      intro z hz
      obtain ⟨i, hiG, hzi⟩ := Set.mem_iUnion₂.mp hz
      by_cases hi0 : i = i₀
      · exact Or.inl (hi0 ▸ (interior_subset hzi))
      · exact Or.inr (hIntBad i hiG hi0 hzi)
    calc μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i))
        ≤ μ (P i₀ ∪ (Work.EKLNonExc.Dinj δ)ᶜ) := measure_mono hsub
      _ ≤ μ (P i₀) + μ ((Work.EKLNonExc.Dinj δ)ᶜ) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (room / 2) + ENNReal.ofReal (room / 4) :=
          add_le_add (le_of_lt hPi₀) (le_of_lt hδsmall)
  have hPieceBound : μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i)
      ≤ ENNReal.ofReal (room / 2) + ENNReal.ofReal (room / 4) := by
    have hsub : (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i)
        ⊆ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i)) ∪ (⋃ i, P i \ interior (P i)) := by
      intro z hz
      obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp hz
      by_cases hint : z ∈ interior (P i)
      · exact Or.inl (Set.mem_iUnion₂.mpr ⟨i, hi, hint⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨i, hzi, hint⟩)
    calc μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i)
        ≤ μ ((⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i))
            ∪ (⋃ i, P i \ interior (P i))) := measure_mono hsub
      _ ≤ μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i))
            + μ (⋃ i, P i \ interior (P i)) := measure_union_le _ _
      _ = μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), interior (P i)) := by rw [hunion_int_zero, add_zero]
      _ ≤ _ := hIntBound
  have hbad_small' : μ bad < ENNReal.ofReal ε := by
    have h1 : μ bad ≤ μ ((⋃ j, cell j))ᶜ := measure_mono interior_subset
    have h2 : μ ((⋃ j, cell j))ᶜ
        ≤ μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i) + μ (⋃ i, P i \ interior (P i)) := by
      rw [hcell_eq]
      exact le_trans (measure_mono hdecomp) (measure_union_le _ _)
    calc μ bad
        ≤ μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i) + μ (⋃ i, P i \ interior (P i)) := le_trans h1 h2
      _ = μ (⋃ i ∈ (Goodᶜ : Set (Fin Np)), P i) := by rw [hunion_int_zero, add_zero]
      _ ≤ ENNReal.ofReal (room / 2) + ENNReal.ofReal (room / 4) := hPieceBound
      _ = ENNReal.ofReal (room / 2 + room / 4) :=
          (ENNReal.ofReal_add (by linarith) (by linarith)).symm
      _ < ENNReal.ofReal ε :=
          (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith [hroom_pos, hroom_le])
  -- ## Step 10: the cells' frontiers are null
  have hcellfront : ∀ j, μ (frontier (cell j)) = 0 := fun j =>
    measure_mono_null frontier_interior_subset (hfront_single (idx j))
  have hunion_cellfront : μ (⋃ j, frontier (cell j)) = 0 := by
    rw [measure_iUnion_null_iff]; exact hcellfront
  -- ## Step 11: the CutData
  refine ⟨{ N := m
            cell := cell
            hopen := fun j => isOpen_interior
            hdisj := ?_
            bad := bad
            hbad_meas := isOpen_interior.measurableSet
            hbad_open := isOpen_interior
            hbad_disj := ?_
            hcover := ?_
            ρ := t / 10
            hρ := by positivity
            g := gg
            hg_mem := fun j => by rw [hgg]; exact (hyv j).1
            lift := liftF
            lift_mk := ?_
            lift_bdd := ?_
            lift_uniq := ?_
            lift_eq := ?_
            c := cp
            hthin := ?_
            hthin_bad := ?_
            hbad_small := hbad_small' }, ?_⟩
  · -- hdisj
    intro i j hij
    have hidx : idx i ≠ idx j := fun h => hij (hidxinj h)
    exact (hPdisj _ _ hidx).mono interior_subset interior_subset
  · -- hbad_disj
    intro j
    rw [Set.disjoint_left]
    intro z hz hzb
    exact (interior_subset hzb) (Set.mem_iUnion.mpr ⟨j, hz⟩)
  · -- hcover
    have hsub : ((⋃ j, cell j) ∪ bad)ᶜ ⊆ ⋃ j, frontier (cell j) := by
      intro z hz
      have hz1 : z ∉ ⋃ j, cell j := fun h => hz (Or.inl h)
      have hz2 : z ∉ bad := fun h => hz (Or.inr h)
      have hcl : z ∈ closure (⋃ j, cell j) := by
        have hmem : z ∉ interior ((⋃ j, cell j))ᶜ := hz2
        rw [interior_compl] at hmem
        simpa using hmem
      have hcl2 : z ∈ ⋃ j, closure (cell j) := by
        have hc : closure (⋃ j, cell j) = ⋃ j, closure (cell j) := by
          have h := Set.Finite.closure_biUnion (Set.finite_univ : (Set.Finite (Set.univ : Set (Fin m))))
            (fun j => cell j)
          simpa using h
        rwa [hc] at hcl
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hcl2
      refine Set.mem_iUnion.mpr ⟨j, ?_⟩
      rw [frontier_eq_closure_inter_closure]
      exact ⟨hj, subset_closure (fun h => hz1 (Set.mem_iUnion.mpr ⟨j, h⟩))⟩
    exact measure_mono_null hsub hunion_cellfront
  · -- lift_mk
    intro j z hz
    have hw := (hliftF_spec j z hz)
    calc mkX (liftF j z)
        = mkX (Classical.choose (hcell_ball j hz) * gg j) := by rw [hliftF_mem j z hz]
      _ = Classical.choose (hcell_ball j hz) • mkX (gg j) :=
          Work.EKLContract.Lemmas.mkX_mul _ _
      _ = Classical.choose (hcell_ball j hz) • yv j := by rw [hgg]
      _ = z := hw.2
  · -- lift_bdd
    intro j z hz
    rw [hρ10]
    exact ⟨Classical.choose (hcell_ball j hz), (hliftF_spec j z hz).1,
      (hliftF_mem j z hz).symm⟩
  · -- lift_uniq
    intro j z hz w hw hwV
    rw [hρ10] at hwV
    obtain ⟨a, ha, haw⟩ := hwV
    have h1 : a • yv j = z := by
      have h2 : a • yv j = a • mkX (gg j) := by rw [hgg]
      exact h2.trans (by rw [← Work.EKLContract.Lemmas.mkX_mul, haw, hw])
    have h2 : a = Classical.choose (hcell_ball j hz) :=
      hinj_y j t htpos ht10 (by rw [htdef]; linarith [h196]) a
        (Classical.choose (hcell_ball j hz)) ha (hliftF_spec j z hz).1
        (by rw [h1, (hliftF_spec j z hz).2])
    rw [hliftF_mem j z hz, ← haw, h2]
  · -- lift_eq
    intro j x hx hfree y hy u huV huU hxy
    rw [hρ10] at huV
    have hax : Classical.choose (hcell_ball j hx) • yv j = x := (hliftF_spec j x hx).2
    have hby : Classical.choose (hcell_ball j hy) • yv j = y := (hliftF_spec j y hy).2
    have hmem1 : u * Classical.choose (hcell_ball j hx) ∈ V (5 * t) :=
      V_mul_aux htpos ht1 huV (hliftF_spec j x hx).1
    have hmem2 : Classical.choose (hcell_ball j hy) ∈ V (5 * t) := fun a b =>
      lt_of_lt_of_le ((hliftF_spec j y hy).1 a b) (by linarith)
    have heq : (u * Classical.choose (hcell_ball j hx)) • yv j
        = Classical.choose (hcell_ball j hy) • yv j := by
      rw [mul_smul, hax, hby, hxy]
    have hres : u * Classical.choose (hcell_ball j hx) = Classical.choose (hcell_ball j hy) :=
      hinj_y j (5 * t) (by positivity) h5t10 h70 _
        (Classical.choose (hcell_ball j hy)) hmem1 hmem2 heq
    calc liftF j y = Classical.choose (hcell_ball j hy) * gg j := hliftF_mem j y hy
      _ = (u * Classical.choose (hcell_ball j hx)) * gg j := by rw [hres]
      _ = u * (Classical.choose (hcell_ball j hx) * gg j) := mul_assoc _ _ _
      _ = u * liftF j x := by rw [hliftF_mem j x hx]
  · -- hthin
    intro η hη
    have hsub : (⋃ j, VThick η (frontier (cell j)))
        ⊆ (⋃ i, VThick η (frontier (P i))) := by
      refine Set.iUnion_subset fun j => ?_
      exact subset_trans (VThick_mono_right frontier_interior_subset η)
        (Set.subset_iUnion (fun i => VThick η (frontier (P i))) (idx j))
    exact le_trans (measure_mono hsub) (by simpa only [VThick_def] using hPthin η hη)
  · -- hthin_bad
    intro η hη
    have hsub : VThick η (frontier bad) ⊆ ⋃ j, VThick η (frontier (cell j)) := by
      rw [← VThick_iUnion η (fun j => frontier (cell j))]
      refine VThick_mono_right ?_ η
      have h1 : frontier (interior ((⋃ j, cell j))ᶜ) ⊆ frontier (((⋃ j, cell j))ᶜ) :=
        frontier_interior_subset
      have h2 : frontier (((⋃ j, cell j))ᶜ) = frontier (⋃ j, cell j) := frontier_compl _
      have h3 : frontier (⋃ j, cell j) ⊆ ⋃ j, frontier (cell j) := by
        intro w hw
        rw [frontier_eq_closure_inter_closure] at hw
        obtain ⟨hwcl, hwint⟩ := hw
        have hc : closure (⋃ j, cell j) = ⋃ j, closure (cell j) := by
          have h := Set.Finite.closure_biUnion (Set.finite_univ : (Set.Finite (Set.univ : Set (Fin m))))
            (fun j => cell j)
          simpa using h
        rw [hc] at hwcl
        obtain ⟨j, hjcl⟩ := Set.mem_iUnion.mp hwcl
        refine Set.mem_iUnion.mpr ⟨j, ?_⟩
        rw [frontier_eq_closure_inter_closure]
        have hwint' : w ∈ (interior (⋃ j, cell j))ᶜ := by
          simpa only [closure_compl] using hwint
        refine ⟨hjcl, ?_⟩
        rw [closure_compl]
        exact fun hzin => hwint' (interior_mono (Set.subset_iUnion (fun j => cell j) j) hzin)
      exact fun z hz => h3 (h2 ▸ h1 hz)
    have hsub2 : (⋃ j, VThick η (frontier (cell j)))
        ⊆ (⋃ i, VThick η (frontier (P i))) := by
      refine Set.iUnion_subset fun j => ?_
      exact subset_trans (VThick_mono_right frontier_interior_subset η)
        (Set.subset_iUnion (fun i => VThick η (frontier (P i))) (idx j))
    exact le_trans (measure_mono (hsub.trans hsub2)) (by simpa only [VThick_def] using hPthin η hη)
  · -- S.ρ ≤ ρ
    show t / 10 ≤ ρ
    rw [htdef]; linarith [hrρ]

end

end Work.EKLC6Core

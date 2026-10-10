import Mathlib.Tactic.Have
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Dynamics.Ergodic.Action.Regular
import Submission.NK.NUV2.Geom.cthickening_vadd_smul_subset
import Submission.NK.NUV2.Geom.exists_mem_frontier_dist_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.Geom

open MeasureTheory Function
open scoped Classical Pointwise ENNReal

/-! Port of the proof in `latticeCount_sub_volume_isBigO` to the weaker hypothesis
`NormedSpace ℝ E` (no inner product structure is used anywhere in the argument). -/

theorem coset_exists_volume_cthickening_frontier_vadd_smul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureTheory.MeasureSpace E] [BorelSpace E]
    [MeasureTheory.Measure.IsAddHaarMeasure (MeasureTheory.volume : MeasureTheory.Measure E)]
    {P : Set E}
    (hbd : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      MeasureTheory.volume (Metric.cthickening ε (frontier P)) ≤ ENNReal.ofReal (c * ε)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t δ : ℝ) (w : E), 1 ≤ t → 0 < δ → δ ≤ t →
      MeasureTheory.volume (Metric.cthickening δ (frontier ((fun x : E => w + t • x) '' P)))
        ≤ ENNReal.ofReal (C * δ * t ^ ((Module.finrank ℝ E : ℝ) - 1)) := by
  obtain ⟨c, hcpos, hc⟩ := hbd
  refine ⟨c, hcpos, ?_⟩
  intro t δ w ht hδ hδt
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let f : E → E := fun x => w + t • x
  have hhom : IsHomeomorph f := by
    have hfe : (⇑({ toFun := fun x => w + t • x
                    invFun := fun y => t⁻¹ • (y - w)
                    left_inv := fun x => by
                      show t⁻¹ • (w + t • x - w) = x
                      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht0.ne', one_smul]
                    right_inv := fun y => by
                      show w + t • (t⁻¹ • (y - w)) = y
                      rw [smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
                      abel
                    continuous_toFun := by fun_prop
                    continuous_invFun := by fun_prop } : E ≃ₜ E)) = f := rfl
    exact isHomeomorph_iff_exists_homeomorph.mpr ⟨_, hfe⟩
  have hfront : f '' frontier P = frontier (f '' P) := hhom.image_frontier P
  have hsub : Metric.cthickening δ (frontier (f '' P)) ⊆
      f '' Metric.cthickening (δ / t) (frontier P) := by
    rw [← hfront]
    exact cthickening_vadd_smul_subset ht0 w
  have hvol : MeasureTheory.volume (f '' Metric.cthickening (δ / t) (frontier P))
      = ENNReal.ofReal (t ^ Module.finrank ℝ E) *
        MeasureTheory.volume (Metric.cthickening (δ / t) (frontier P)) := by
    have himg : f '' Metric.cthickening (δ / t) (frontier P)
        = (fun z : E => w + z) '' (t • Metric.cthickening (δ / t) (frontier P)) := by
      rw [show f = (fun z : E => w + z) ∘ (fun x : E => t • x) from rfl,
        Set.image_comp, Set.image_smul]
    rw [himg, Set.image_add_left, MeasureTheory.measure_preimage_add MeasureTheory.volume (-w),
      MeasureTheory.Measure.addHaar_smul MeasureTheory.volume t,
      abs_of_nonneg (pow_nonneg ht0.le _)]
  calc MeasureTheory.volume (Metric.cthickening δ (frontier (f '' P)))
      ≤ MeasureTheory.volume (f '' Metric.cthickening (δ / t) (frontier P)) :=
        MeasureTheory.measure_mono hsub
    _ = ENNReal.ofReal (t ^ Module.finrank ℝ E) *
          MeasureTheory.volume (Metric.cthickening (δ / t) (frontier P)) := hvol
    _ ≤ ENNReal.ofReal (t ^ Module.finrank ℝ E) * ENNReal.ofReal (c * (δ / t)) :=
        mul_le_mul_right (hc (δ / t) (div_pos hδ ht0) ((div_le_one ht0).mpr hδt)) _
    _ = ENNReal.ofReal (c * δ * t ^ ((Module.finrank ℝ E : ℝ) - 1)) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg ht0.le _)]
        congr 1
        rw [Real.rpow_sub ht0 (Module.finrank ℝ E : ℝ) 1, Real.rpow_one, Real.rpow_natCast,
          div_eq_mul_inv, div_eq_mul_inv]
        ring


set_option autoImplicit false

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]

/-- The set of lattice points of a bounded set is finite. -/
lemma coset_finite_setOf_coe_mem (L : Submodule ℤ E) [DiscreteTopology L]
    {A : Set E} (hA : Bornology.IsBounded A) :
    ({l : L | ((l : L) : E) ∈ A} : Set L).Finite := by
  have hclosed : IsClosed (L : Set E) := by
    have : DiscreteTopology L.toAddSubgroup := inferInstance
    exact AddSubgroup.isClosed_of_discreteTopology (U := L.toAddSubgroup)
  have hInt : (A ∩ (L : Set E)).Finite :=
    Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete hA hclosed
  refine Set.Finite.of_finite_image ?_ Subtype.coe_injective.injOn
  have himg : (Subtype.val '' {l : L | ((l : L) : E) ∈ A}) = (L : Set E) ∩ A := by
    ext x; constructor
    · rintro ⟨l, hl, rfl⟩; exact ⟨l.2, hl⟩
    · rintro ⟨hxL, hxA⟩; exact ⟨⟨x, hxL⟩, hxA, rfl⟩
  rw [himg, Set.inter_comm]
  exact hInt

/-- The measure of a finite union of pairwise a.e. disjoint translates of a fundamental domain. -/
theorem coset_measureReal_iUnion_vadd_fundamentalDomain
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (F : Set E) (hF : IsAddFundamentalDomain L F volume) (hFmeas : MeasurableSet F)
    (hFbdd : Bornology.IsBounded F) {S : Set L} (hSfin : S.Finite) :
    volume.real (⋃ l : S, ((l : L) : E) +ᵥ F) = (Nat.card S : ℝ) * volume.real F := by
  classical
  have : Fintype S := hSfin.fintype
  have hfin : volume F ≠ ∞ := ne_of_lt (hFbdd.measure_lt_top (μ := volume))
  have hd : Set.Pairwise (↑(Finset.univ : Finset S))
      (Function.onFun (AEDisjoint volume) fun l : S => ((l : L) : E) +ᵥ F) := by
    intro a _ b _ hab
    exact hF.aedisjoint (Subtype.coe_injective.ne hab)
  have hm : ∀ b ∈ (Finset.univ : Finset S), NullMeasurableSet (((b : L) : E) +ᵥ F) volume := by
    intro b _
    exact (hFmeas.const_vadd ((b : L) : E)).nullMeasurableSet
  have hne : ∀ b ∈ (Finset.univ : Finset S), volume (((b : L) : E) +ᵥ F) ≠ ∞ := by
    intro b _
    rw [measure_vadd volume ((b : L) : E) F]
    exact hfin
  have key := measureReal_biUnion_finset₀ (μ := volume) (s := (Finset.univ : Finset S))
      (f := fun l : S => ((l : L) : E) +ᵥ F) hd hm hne
  have e1 : (⋃ l ∈ (Finset.univ : Finset S), ((l : L) : E) +ᵥ F)
      = ⋃ l : S, ((l : L) : E) +ᵥ F := by simp
  have hpt : ∀ l : S, volume.real (((l : L) : E) +ᵥ F) = volume.real F := by
    intro l
    rw [measureReal_def, measureReal_def, measure_vadd volume ((l : L) : E) F]
  rw [← e1, key]
  simp only [hpt, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- Counting lattice points: the upper bound. -/
theorem coset_card_mul_le_measureReal_add_sub
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (F : Set E) (hF : IsAddFundamentalDomain L F volume) (hFmeas : MeasurableSet F)
    (hFbdd : Bornology.IsBounded F) (hF0 : (0 : E) ∈ F)
    {A : Set E} (hA : Bornology.IsBounded A) :
    (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F ≤ volume.real (A + (F - F)) := by
  classical
  have hSfin : ({l : L | ((l : L) : E) ∈ A} : Set L).Finite := coset_finite_setOf_coe_mem L hA
  have key := coset_measureReal_iUnion_vadd_fundamentalDomain L F hF hFmeas hFbdd hSfin
  have hsub : (⋃ l : {x : L // (x : E) ∈ A}, ((l : L) : E) +ᵥ F) ⊆ A + (F - F) := by
    refine Set.iUnion_subset fun l => ?_
    intro x hx
    obtain ⟨f, hfF, rfl⟩ := hx
    exact Set.mem_add.mpr ⟨(l : L), l.2, f,
      Set.mem_sub.mpr ⟨f, hfF, 0, hF0, by simp⟩, rfl⟩
  calc (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F
      = volume.real (⋃ l : {x : L // (x : E) ∈ A}, ((l : L) : E) +ᵥ F) := key.symm
    _ ≤ volume.real (A + (F - F)) :=
        measureReal_mono hsub (ne_of_lt ((hA.add (hFbdd.sub hFbdd)).measure_lt_top (μ := volume)))

/-- Counting lattice points: the lower bound (erosion bound). -/
theorem coset_measureReal_erosion_le_card_mul
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (F : Set E) (hF : IsAddFundamentalDomain L F volume) (hFmeas : MeasurableSet F)
    (hFbdd : Bornology.IsBounded F) (hF0 : (0 : E) ∈ F)
    {A : Set E} (hA : Bornology.IsBounded A) :
    volume.real {x : E | x +ᵥ (F - F) ⊆ A} ≤
      (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F := by
  classical
  have hSfin : ({l : L | ((l : L) : E) ∈ A} : Set L).Finite := coset_finite_setOf_coe_mem L hA
  have key := coset_measureReal_iUnion_vadd_fundamentalDomain L F hF hFmeas hFbdd hSfin
  set S : Set L := {l : L | ((l : L) : E) ∈ A} with hSdef
  set E₀ : Set E := {x : E | ¬ ∃ l : L, x ∈ ((l : L) : E) +ᵥ F} with hE₀def
  have hTU : {x : E | ∃ g : L, g +ᵥ x ∈ F} ⊆ {x : E | ∃ l : L, x ∈ ((l : L) : E) +ᵥ F} := by
    rintro x ⟨g, hg⟩
    exact ⟨-g, ⟨(g : E) + x, hg, by simp⟩⟩
  have hTcompl : volume {x : E | ¬ ∃ g : L, g +ᵥ x ∈ F} = 0 := ae_iff.mp hF.ae_covers
  have hE₀zero : volume E₀ = 0 :=
    measure_mono_null (fun x hx hxT => hx (hTU hxT)) hTcompl
  have hbdd : Bornology.IsBounded (⋃ l : S, ((l : L) : E) +ᵥ F) := by
    refine (hA.add (hFbdd.sub hFbdd)).subset ?_
    refine Set.iUnion_subset fun l => ?_
    intro x hx
    obtain ⟨f, hfF, rfl⟩ := hx
    exact Set.mem_add.mpr ⟨(l : L), l.2, f,
      Set.mem_sub.mpr ⟨f, hfF, 0, hF0, by simp⟩, rfl⟩
  have hsub2 : {x : E | x +ᵥ (F - F) ⊆ A} ⊆
      (⋃ l : S, ((l : L) : E) +ᵥ F) ∪ E₀ := by
    intro y hy
    by_cases hyE : y ∈ E₀
    · exact Or.inr hyE
    · refine Or.inl ?_
      simp only [hE₀def, Set.mem_ofPred_eq, not_not] at hyE
      obtain ⟨l, hl⟩ := hyE
      obtain ⟨f, hfF, hlf⟩ := hl
      refine Set.mem_iUnion.mpr ⟨⟨l, ?_⟩, ?_⟩
      · change ((l : L) : E) ∈ A
        have h1 : (l : E) = y + (0 - f) := by rw [← hlf]; simp
        rw [h1]
        exact hy ⟨0 - f, Set.mem_sub.mpr ⟨0, hF0, f, hfF, rfl⟩, rfl⟩
      · exact ⟨f, hfF, hlf⟩
  have hfin : volume ((⋃ l : S, ((l : L) : E) +ᵥ F) ∪ E₀) < ⊤ := by
    refine lt_of_le_of_lt (measure_union_le _ _) ?_
    rw [hE₀zero, add_zero]
    exact hbdd.measure_lt_top (μ := volume)
  calc volume.real {x : E | x +ᵥ (F - F) ⊆ A}
      ≤ volume.real ((⋃ l : S, ((l : L) : E) +ᵥ F) ∪ E₀) :=
        measureReal_mono hsub2 (ne_of_lt hfin)
    _ ≤ volume.real (⋃ l : S, ((l : L) : E) +ᵥ F) + volume.real E₀ := measureReal_union_le _ _
    _ = (Nat.card S : ℝ) * volume.real F := by
        rw [key, show volume.real E₀ = 0 by
          rw [measureReal_def, hE₀zero, ENNReal.toReal_zero], add_zero]

/-- A bounded set which is nonempty lies in a closed ball around any given point. -/
lemma coset_exists_closedBall_superset_of_isBounded (s : Set E) (hs : Bornology.IsBounded s)
    (hsne : s.Nonempty) (x : E) :
    ∃ R : ℝ, 0 < R ∧ s ⊆ Metric.closedBall x R := by
  obtain ⟨a, ha⟩ := hsne
  obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hs
  refine ⟨max (C + dist a x) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun y hy => ?_⟩
  rw [Metric.mem_closedBall]
  have h1 : dist y x ≤ C + dist a x := by
    calc dist y x ≤ dist y a + dist a x := dist_triangle _ _ _
      _ ≤ C + dist a x := by linarith [hC hy ha]
  linarith [le_max_left (C + dist a x) 1]

/-- Points of `A + K` which are not in `A` lie within `delta` of the frontier of `A`, when `K` lies
in the closed ball of radius `delta`. -/
lemma coset_sdiff_add_subset_cthickening_frontier {A K : Set E} {δ : ℝ}
    (hK : K ⊆ Metric.closedBall 0 δ) :
    (A + K) \ A ⊆ Metric.cthickening δ (frontier A) := by
  rintro x ⟨hx, hxA⟩
  obtain ⟨a, ha, k, hk, rfl⟩ := Set.mem_add.mp hx
  have hkδ : ‖k‖ ≤ δ := by
    have h := hK hk
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  obtain ⟨z, hz, -, hzx⟩ := exists_mem_frontier_dist_le ha hxA
  refine Metric.mem_cthickening_of_dist_le (a + k) z δ (frontier A) hz ?_
  calc dist (a + k) z = dist z (a + k) := dist_comm _ _
    _ ≤ dist (a + k) a := hzx
    _ = ‖(a + k) - a‖ := dist_eq_norm _ _
    _ = ‖k‖ := by rw [add_sub_cancel_left]
    _ ≤ δ := hkδ

/-- Points of `A` outside the erosion of `A` by `K` lie within `delta` of the frontier of `A`, when
`K` lies in the closed ball of radius `delta`. -/
lemma coset_sdiff_erosion_subset_cthickening_frontier {A K : Set E} {δ : ℝ}
    (hK : K ⊆ Metric.closedBall 0 δ) :
    A \ {x : E | x +ᵥ K ⊆ A} ⊆ Metric.cthickening δ (frontier A) := by
  rintro x ⟨hxA, hxE⟩
  have hex : ∃ y ∈ x +ᵥ K, y ∉ A := by
    by_contra h
    exact hxE fun y hy => by by_contra hyA; exact h ⟨y, hy, hyA⟩
  obtain ⟨y, hyK, hyA⟩ := hex
  obtain ⟨k, hk, rfl⟩ := hyK
  have hkδ : ‖k‖ ≤ δ := by
    have h := hK hk
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  obtain ⟨z, hz, hzx, -⟩ := exists_mem_frontier_dist_le hxA hyA
  refine Metric.mem_cthickening_of_dist_le x z δ (frontier A) hz ?_
  calc dist x z = dist z x := dist_comm _ _
    _ ≤ dist (x + k) x := hzx
    _ = ‖(x + k) - x‖ := dist_eq_norm _ _
    _ = ‖k‖ := by rw [add_sub_cancel_left]
    _ ≤ δ := hkδ

end Helpers

theorem latticeCosetCount_sub_volume_isBigO
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (P : Set E) (hPbdd : Bornology.IsBounded P) (hPmeas : MeasurableSet P)
    (hbd : ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      volume (Metric.cthickening ε (frontier P)) ≤ ENNReal.ofReal (c * ε))
    (v : E) :
    ∃ C : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      |((Nat.card {x : L // v + (x : E) ∈ (Y ^ (Module.finrank ℝ E : ℝ)⁻¹) • P} : ℝ)
        - Y * (volume P).toReal / ZLattice.covolume L)|
      ≤ C * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) := by
  classical
  by_cases hn : Module.finrank ℝ E = 0
  · have hYpow : ∀ Y : ℝ, Y ^ ((Module.finrank ℝ E : ℝ)⁻¹) = 1 := by
      intro Y; rw [hn]; simp
    refine ⟨(Nat.card {x : L // v + (x : E) ∈ P} : ℝ)
      + (volume P).toReal / ZLattice.covolume L + 1, ?_, ?_⟩
    · have hD := ZLattice.covolume_pos L volume
      have hN : (0 : ℝ) ≤ (Nat.card {x : L // v + (x : E) ∈ P} : ℝ) := Nat.cast_nonneg _
      have hV : 0 ≤ (volume P).toReal := ENNReal.toReal_nonneg
      have hq : 0 ≤ (volume P).toReal / ZLattice.covolume L := div_nonneg hV hD.le
      linarith
    · intro Y hY
      have hset : (Y ^ ((Module.finrank ℝ E : ℝ)⁻¹)) • P = P := by rw [hYpow Y, one_smul]
      have hexp : 1 - (Module.finrank ℝ E : ℝ)⁻¹ = 1 := by rw [hn]; norm_num
      rw [hset, hexp, Real.rpow_one]
      set N : ℝ := (Nat.card {x : L // v + (x : E) ∈ P} : ℝ) with hNdef
      set q : ℝ := (volume P).toReal / ZLattice.covolume L with hqdef
      rw [show Y * (volume P).toReal / ZLattice.covolume L volume
          = Y * ((volume P).toReal / ZLattice.covolume L volume) by ring]
      have hDpos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L volume
      have hNnn : 0 ≤ N := Nat.cast_nonneg _
      have hqnn : 0 ≤ q := div_nonneg ENNReal.toReal_nonneg hDpos.le
      have hYnn : 0 ≤ Y := le_trans zero_le_one hY
      have h1 : |N - Y * q| ≤ N + Y * q := by
        rw [abs_sub_le_iff]
        constructor <;> nlinarith [mul_nonneg hYnn hqnn, hNnn]
      refine h1.trans ?_
      have hNY : N ≤ N * Y := le_mul_of_one_le_right hNnn hY
      have hqY : Y * q ≤ q * Y := by rw [mul_comm]
      calc N + Y * q = (N + Y * q) + 0 := by ring
        _ ≤ (N * Y + q * Y) + Y := add_le_add (add_le_add hNY hqY) hYnn
        _ = (N + q + 1) * Y := by ring
  · have hnpos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hn
    obtain ⟨C₀, hC₀pos, hC₀le⟩ := coset_exists_volume_cthickening_frontier_vadd_smul_le (P := P) hbd
    let b := Module.Free.chooseBasis ℤ L
    let bR := b.ofZLatticeBasis ℝ L
    let F : Set E := ZSpan.fundamentalDomain bR
    have hF : IsAddFundamentalDomain L F volume := ZLattice.isAddFundamentalDomain b volume
    have hFmeas : MeasurableSet F := ZSpan.fundamentalDomain_measurableSet bR
    have hFbdd : Bornology.IsBounded F := ZSpan.fundamentalDomain_isBounded bR
    have hF0 : (0 : E) ∈ F := by
      rw [ZSpan.mem_fundamentalDomain]
      intro i
      simp [Set.mem_Ico]
    have hcov : ZLattice.covolume L = volume.real F :=
      ZLattice.covolume_eq_measure_fundamentalDomain L volume hF
    have hDpos : 0 < volume.real F := by
      rw [← hcov]; exact ZLattice.covolume_pos L volume
    by_cases hPne : P.Nonempty
    · obtain ⟨δ, hδpos, hδF⟩ : ∃ δ : ℝ, 0 < δ ∧ F - F ⊆ Metric.closedBall 0 δ :=
        coset_exists_closedBall_superset_of_isBounded (F - F) (hFbdd.sub hFbdd)
          ⟨0, Set.mem_sub.mpr ⟨0, hF0, 0, hF0, sub_self 0⟩⟩ 0
      obtain ⟨R_P, hR_Ppos, hPsub⟩ : ∃ R : ℝ, 0 < R ∧ P ⊆ Metric.closedBall 0 R :=
        coset_exists_closedBall_superset_of_isBounded P hPbdd hPne 0
      let M : ℝ := max δ (δ ^ Module.finrank ℝ E)
      let B : Set E := Metric.closedBall 0 (‖v‖ + M * R_P)
      let N₁ : ℝ := (Nat.card {x : L // (x : E) ∈ B} : ℝ)
      let Cbig : ℝ := (C₀ * δ) / volume.real F
        + (N₁ + δ ^ Module.finrank ℝ E * (volume P).toReal / volume.real F) + 1
      have hN₁nn : 0 ≤ N₁ := Nat.cast_nonneg _
      have hδpownn : 0 ≤ δ ^ Module.finrank ℝ E := pow_nonneg hδpos.le _
      have hdivnn : 0 ≤ δ ^ Module.finrank ℝ E * (volume P).toReal / volume.real F :=
        div_nonneg (mul_nonneg hδpownn ENNReal.toReal_nonneg) hDpos.le
      have hCbigge : (C₀ * δ) / volume.real F ≤ Cbig := by
        simp only [Cbig]; linarith [hN₁nn, hdivnn]
      have hCbigge2 : N₁ + δ ^ Module.finrank ℝ E * (volume P).toReal / volume.real F ≤ Cbig := by
        have h1 : 0 ≤ (C₀ * δ) / volume.real F := div_nonneg (mul_nonneg hC₀pos.le hδpos.le) hDpos.le
        simp only [Cbig]; linarith
      have hCbigpos : 0 < Cbig := by
        have h1 : 0 ≤ (C₀ * δ) / volume.real F := div_nonneg (mul_nonneg hC₀pos.le hδpos.le) hDpos.le
        simp only [Cbig]; linarith [hN₁nn, hdivnn]
      refine ⟨Cbig, hCbigpos, ?_⟩
      intro Y hY
      let t : ℝ := Y ^ ((Module.finrank ℝ E : ℝ)⁻¹)
      have ht1 : 1 ≤ t := Real.one_le_rpow hY (inv_nonneg.mpr (Nat.cast_nonneg _))
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
      have htn : t ^ (Module.finrank ℝ E : ℝ) = Y := by
        rw [Real.rpow_natCast]
        exact Real.rpow_inv_natCast_pow (le_trans zero_le_one hY) hn
      let A : Set E := (fun y : E => -v + t • y) '' P
      have hAsub : A ⊆ Metric.closedBall 0 (‖v‖ + t * R_P) := by
        rintro x ⟨y, hyP, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        have hyR : ‖y‖ ≤ R_P := by
          have h := hPsub hyP
          rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
        calc ‖-v + t • y‖ ≤ ‖-v‖ + ‖t • y‖ := norm_add_le _ _
          _ = ‖v‖ + t * ‖y‖ := by rw [norm_neg, norm_smul, Real.norm_of_nonneg htpos.le]
          _ ≤ ‖v‖ + t * R_P := by linarith [mul_le_mul_of_nonneg_left hyR htpos.le]
      have hAbdd : Bornology.IsBounded A := Metric.isBounded_closedBall.subset hAsub
      have hAmeas : MeasurableSet A := by
        have hmap : MeasurableEmbedding (fun y : E => -v + t • y) :=
          ((Homeomorph.smulOfNeZero t htpos.ne').trans (Homeomorph.addLeft (-v))).measurableEmbedding
        exact hmap.measurableSet_image.mpr hPmeas
      have hAmem : ∀ x : L, ((x : E) ∈ A ↔ v + (x : E) ∈ t • P) := by
        intro x
        constructor
        · rintro ⟨y, hyP, hyx⟩
          refine ⟨y, hyP, ?_⟩
          show t • y = v + (x : E)
          rw [← hyx]; simp
        · rintro ⟨y, hyP, hyx⟩
          refine ⟨y, hyP, ?_⟩
          show -v + t • y = (x : E)
          have hyx' : t • y = v + (x : E) := hyx
          rw [hyx']; simp
      have hcard : Nat.card {x : L // v + (x : E) ∈ (Y ^ ((Module.finrank ℝ E : ℝ)⁻¹)) • P}
          = Nat.card {x : L // (x : E) ∈ A} := by
        refine Nat.card_congr (Equiv.subtypeEquivRight ?_)
        intro x
        exact (hAmem x).symm
      have hvolA : volume.real A = Y * (volume P).toReal := by
        have hAeq : A = (-v) +ᵥ (t • P) := by
          ext x
          constructor
          · rintro ⟨y, hyP, rfl⟩
            exact ⟨t • y, ⟨y, hyP, rfl⟩, rfl⟩
          · rintro ⟨z, hz, hzx⟩
            obtain ⟨y, hyP, rfl⟩ := hz
            exact ⟨y, hyP, hzx⟩
        have h1 : (volume : Measure E) A = (volume : Measure E) (t • P) := by
          rw [hAeq, measure_vadd volume (-v) (t • P)]
        have h2 : (volume : Measure E) (t • P) = ENNReal.ofReal Y * volume P := by
          rw [Measure.addHaar_smul_of_nonneg volume htpos.le P]
          rw [← Real.rpow_natCast, htn]
        rw [measureReal_def, h1, h2, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (le_trans zero_le_one hY)]
      rw [hcard, hcov]
      by_cases hδt : δ ≤ t
      · have hlayer : volume.real (Metric.cthickening δ (frontier A))
            ≤ C₀ * δ * t ^ ((Module.finrank ℝ E : ℝ) - 1) := by
          have h := hC₀le t δ (-v) ht1 hδpos hδt
          have h' : volume.real (Metric.cthickening δ (frontier A))
              ≤ (ENNReal.ofReal (C₀ * δ * t ^ ((Module.finrank ℝ E : ℝ) - 1))).toReal := by
            rw [measureReal_def]
            exact ENNReal.toReal_mono (by simp) h
          rwa [ENNReal.toReal_ofReal (by positivity)] at h'
        have hcle := coset_card_mul_le_measureReal_add_sub L F hF hFmeas hFbdd hF0 hAbdd
        have hcge := coset_measureReal_erosion_le_card_mul L F hF hFmeas hFbdd hF0 hAbdd
        have herosion_sub : {x : E | x +ᵥ (F - F) ⊆ A} ⊆ A := by
          intro x hx
          exact hx ⟨0, Set.mem_sub.mpr ⟨0, hF0, 0, hF0, sub_self 0⟩, by simp⟩
        have hcthick_bdd : Bornology.IsBounded (Metric.cthickening δ (frontier A)) :=
          (hAbdd.closure.subset frontier_subset_closure).cthickening
        have hsub3 : A + (F - F) ⊆ A ∪ Metric.cthickening δ (frontier A) := by
          intro x hx
          by_cases hxA : x ∈ A
          · exact Or.inl hxA
          · exact Or.inr (coset_sdiff_add_subset_cthickening_frontier hδF ⟨hx, hxA⟩)
        have hsub4 : A ⊆ {x : E | x +ᵥ (F - F) ⊆ A} ∪ Metric.cthickening δ (frontier A) := by
          intro x hx
          by_cases hxE : x +ᵥ (F - F) ⊆ A
          · exact Or.inl hxE
          · exact Or.inr (coset_sdiff_erosion_subset_cthickening_frontier hδF ⟨hx, hxE⟩)
        have hfin3 : volume (A ∪ Metric.cthickening δ (frontier A)) ≠ ∞ :=
          ne_of_lt ((hAbdd.union hcthick_bdd).measure_lt_top (μ := volume))
        have hfin4 : volume ({x : E | x +ᵥ (F - F) ⊆ A} ∪ Metric.cthickening δ (frontier A))
            ≠ ∞ :=
          ne_of_lt (((hAbdd.subset herosion_sub).union hcthick_bdd).measure_lt_top (μ := volume))
        have hupper : (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F
            ≤ volume.real A + volume.real (Metric.cthickening δ (frontier A)) :=
          calc (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F
              ≤ volume.real (A + (F - F)) := hcle
            _ ≤ volume.real (A ∪ Metric.cthickening δ (frontier A)) := measureReal_mono hsub3 hfin3
            _ ≤ volume.real A + volume.real (Metric.cthickening δ (frontier A)) :=
                measureReal_union_le _ _
        have hlower : volume.real A ≤ (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F
            + volume.real (Metric.cthickening δ (frontier A)) :=
          calc volume.real A
              ≤ volume.real ({x : E | x +ᵥ (F - F) ⊆ A} ∪ Metric.cthickening δ (frontier A)) :=
                measureReal_mono hsub4 hfin4
            _ ≤ volume.real {x : E | x +ᵥ (F - F) ⊆ A}
                  + volume.real (Metric.cthickening δ (frontier A)) := measureReal_union_le _ _
            _ ≤ (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F
                  + volume.real (Metric.cthickening δ (frontier A)) := by linarith [hcge]
        have habs : |(Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F - volume.real A|
            ≤ volume.real (Metric.cthickening δ (frontier A)) := by
          rw [abs_le]
          constructor <;> linarith [hupper, hlower]
        have hdiv : |(Nat.card {x : L // (x : E) ∈ A} : ℝ) - volume.real A / volume.real F|
            ≤ volume.real (Metric.cthickening δ (frontier A)) / volume.real F := by
          have heq : ((Nat.card {x : L // (x : E) ∈ A} : ℝ) - volume.real A / volume.real F)
                * volume.real F
              = (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F - volume.real A := by
            calc ((Nat.card {x : L // (x : E) ∈ A} : ℝ) - volume.real A / volume.real F)
                  * volume.real F
                = (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F
                  - volume.real A / volume.real F * volume.real F := by rw [sub_mul]
              _ = (Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F - volume.real A := by
                  rw [div_mul_cancel₀ _ hDpos.ne']
          have h1 : |(Nat.card {x : L // (x : E) ∈ A} : ℝ) * volume.real F - volume.real A|
              = |(Nat.card {x : L // (x : E) ∈ A} : ℝ) - volume.real A / volume.real F|
                * volume.real F := by
            rw [← heq, abs_mul, abs_of_pos hDpos]
          rw [h1] at habs
          rw [le_div_iff₀ hDpos]
          exact habs
        rw [hvolA] at hdiv
        have hexp : t ^ ((Module.finrank ℝ E : ℝ) - 1)
            = Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) := by
          rw [Real.rpow_sub htpos, Real.rpow_sub (zero_lt_one.trans_le hY), Real.rpow_one,
            Real.rpow_one, htn]
        have hLdiv : volume.real (Metric.cthickening δ (frontier A)) / volume.real F
            ≤ (C₀ * δ / volume.real F) * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) := by
          have hL : volume.real (Metric.cthickening δ (frontier A))
              ≤ C₀ * δ * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) := by
            rw [← hexp]; exact hlayer
          calc volume.real (Metric.cthickening δ (frontier A)) / volume.real F
              ≤ (C₀ * δ * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹)) / volume.real F :=
                div_le_div_of_nonneg_right hL hDpos.le
            _ = (C₀ * δ / volume.real F) * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) := by ring
        calc |(Nat.card {x : L // (x : E) ∈ A} : ℝ) - Y * (volume P).toReal / volume.real F|
            ≤ volume.real (Metric.cthickening δ (frontier A)) / volume.real F := hdiv
          _ ≤ (C₀ * δ / volume.real F) * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) := hLdiv
          _ ≤ Cbig * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_right hCbigge
                (Real.rpow_nonneg (le_trans zero_le_one hY) _)
      · rw [not_le] at hδt
        have hYlt : Y < δ ^ Module.finrank ℝ E := by
          rw [← Real.rpow_natCast, ← htn]
          exact Real.rpow_lt_rpow htpos.le hδt (by exact_mod_cast hnpos)
        have hAB : A ⊆ B := by
          intro x hx
          have hx' := hAsub hx
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx' ⊢
          have htM : t ≤ M := le_trans hδt.le (le_max_left _ _)
          calc ‖x‖ ≤ ‖v‖ + t * R_P := hx'
            _ ≤ ‖v‖ + M * R_P := by linarith [mul_le_mul_of_nonneg_right htM hR_Ppos.le]
        have hNB : (Nat.card {x : L // (x : E) ∈ A} : ℝ) ≤ N₁ := by
          haveI : Finite {x : L // (x : E) ∈ B} :=
            (coset_finite_setOf_coe_mem L Metric.isBounded_closedBall).to_subtype
          have hle : Nat.card {x : L // (x : E) ∈ A} ≤ Nat.card {x : L // (x : E) ∈ B} :=
            Nat.card_le_card_of_injective
              (fun x : {x : L // (x : E) ∈ A} => (⟨x.1, hAB x.2⟩ : {x : L // (x : E) ∈ B}))
              (fun a b hab =>
                Subtype.ext (congrArg (fun x : {x : L // (x : E) ∈ B} => (x : L)) hab))
          show (Nat.card {x : L // (x : E) ∈ A} : ℝ) ≤ (Nat.card {x : L // (x : E) ∈ B} : ℝ)
          exact_mod_cast hle
        have hYdiv : Y * (volume P).toReal / volume.real F
            ≤ δ ^ Module.finrank ℝ E * (volume P).toReal / volume.real F := by
          refine div_le_div_of_nonneg_right ?_ hDpos.le
          exact mul_le_mul_of_nonneg_right hYlt.le ENNReal.toReal_nonneg
        have hexpnn : 0 ≤ (1 : ℝ) - (Module.finrank ℝ E : ℝ)⁻¹ := by
          have h1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hnpos
          have h2 : (Module.finrank ℝ E : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
          linarith
        have hone : (1 : ℝ) ≤ Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) :=
          Real.one_le_rpow hY hexpnn
        have h1 : |(Nat.card {x : L // (x : E) ∈ A} : ℝ) - Y * (volume P).toReal / volume.real F|
            ≤ (Nat.card {x : L // (x : E) ∈ A} : ℝ) + Y * (volume P).toReal / volume.real F := by
          have hnn : 0 ≤ Y * (volume P).toReal / volume.real F :=
            div_nonneg (mul_nonneg (le_trans zero_le_one hY) ENNReal.toReal_nonneg) hDpos.le
          rw [abs_sub_le_iff]
          constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.card {x : L // (x : E) ∈ A})]
        calc |(Nat.card {x : L // (x : E) ∈ A} : ℝ) - Y * (volume P).toReal / volume.real F|
            ≤ (Nat.card {x : L // (x : E) ∈ A} : ℝ) + Y * (volume P).toReal / volume.real F := h1
          _ ≤ N₁ + δ ^ Module.finrank ℝ E * (volume P).toReal / volume.real F := by linarith [hNB, hYdiv]
          _ ≤ Cbig := hCbigge2
          _ ≤ Cbig * Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) :=
              le_mul_of_one_le_right hCbigpos.le hone
    · rw [Set.not_nonempty_iff_eq_empty] at hPne
      refine ⟨1, one_pos, ?_⟩
      intro Y hY
      rw [hPne]
      have hsm : (Y ^ ((Module.finrank ℝ E : ℝ)⁻¹)) • (∅ : Set E) = ∅ := Set.smul_set_empty
      rw [hsm]
      have hcard0 : Nat.card {x : L // v + (x : E) ∈ (∅ : Set E)} = 0 := by simp
      rw [hcard0, Nat.cast_zero, measure_empty, ENNReal.toReal_zero]
      have hone : (0 : ℝ) ≤ Y ^ (1 - (Module.finrank ℝ E : ℝ)⁻¹) :=
        Real.rpow_nonneg (le_trans zero_le_one hY) _
      simp only [mul_zero, zero_div, sub_self, abs_zero, one_mul]
      exact hone

end NK.NUV2.Geom

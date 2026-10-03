import Mathlib
import Submission.Work.HornSC.Tools
import Submission.Work.PlanarSC.jordan_criterion_simplyConnected
import Submission.Work.HornSC.JC.exists_injective_lift
import Submission.Work.HornSC.JC.closure_componentIn_inter
import Submission.Work.HornSC.JC.componentIn_unbounded_of_halfplane
import Submission.Work.HornSC.JC.isConnected_diff_singleton

set_option maxHeartbeats 4000000

namespace Work.HornSC

open Set

open scoped Pointwise
open scoped _root_.Topology
open Filter

noncomputable section


/-! ### Auxiliary lemmas -/

/-- **The `2πi`-translates of a connected compact set lie in the unbounded component of its
complement**, when they are disjoint from it. -/
theorem translate_subset_unbounded_of_im {S : Set ℂ} (hScpt : IsCompact S) (hSconn : IsConnected S)
    {y : ℝ} (hy : y ≠ 0) (hdisj : Disjoint S (S + ({(y : ℂ) * Complex.I} : Set ℂ)))
    {q : ℂ} (hq : q ∈ S + ({(y : ℂ) * Complex.I} : Set ℂ)) :
    ¬ Bornology.IsBounded (connectedComponentIn Sᶜ q) := by
  have hSne : S.Nonempty := hSconn.nonempty
  have hTconn : IsPreconnected (S + ({(y : ℂ) * Complex.I} : Set ℂ)) := by
    have h := hSconn.isPreconnected.image (fun z : ℂ => z + (y : ℂ) * Complex.I) (by fun_prop)
    rwa [show (fun z : ℂ => z + (y : ℂ) * Complex.I) '' S
        = S + ({(y : ℂ) * Complex.I} : Set ℂ) from by
      ext x; simp [Set.mem_add]] at h
  have hTsub : S + ({(y : ℂ) * Complex.I} : Set ℂ) ⊆ Sᶜ := by
    intro z hz hzS
    exact Set.disjoint_left.mp hdisj hzS hz
  suffices hex : ∃ q₀ ∈ S + ({(y : ℂ) * Complex.I} : Set ℂ),
      ¬ Bornology.IsBounded (connectedComponentIn Sᶜ q₀) by
    obtain ⟨q₀, hq₀, hq₀nb⟩ := hex
    have h1 : q ∈ connectedComponentIn Sᶜ q₀ := hTconn.subset_connectedComponentIn hq₀ hTsub hq
    rw [← connectedComponentIn_eq h1]
    exact hq₀nb
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · obtain ⟨p, hpS, hpmin⟩ := hScpt.exists_isMinOn hSne Complex.continuous_im.continuousOn
    refine ⟨p + (y : ℂ) * Complex.I, ⟨p, hpS, (y : ℂ) * Complex.I, mem_singleton _, by ring⟩, ?_⟩
    refine Work.HornSC.JC.componentIn_unbounded_of_halfplane (Or.inr (Or.inr (Or.inr ?_)))
    intro w hw
    have h1 : p.im ≤ w.im := hpmin hw
    have h2 : (p + (y : ℂ) * Complex.I).im = p.im + y := by simp
    rw [h2]; linarith
  · obtain ⟨p, hpS, hpmax⟩ := hScpt.exists_isMaxOn hSne Complex.continuous_im.continuousOn
    refine ⟨p + (y : ℂ) * Complex.I, ⟨p, hpS, (y : ℂ) * Complex.I, mem_singleton _, by ring⟩, ?_⟩
    refine Work.HornSC.JC.componentIn_unbounded_of_halfplane (Or.inr (Or.inr (Or.inl ?_)))
    intro w hw
    have h1 : w.im ≤ p.im := hpmax hw
    have h2 : (p + (y : ℂ) * Complex.I).im = p.im + y := by simp
    rw [h2]; linarith

end

/-! ### The main theorem -/

/-- **A Jordan curve winds around the points of its interior.** -/
theorem not_hasArg_of_jordan_curve {γ : C(Circle, ℂ)} (hγ : Function.Injective γ)
    {a : ℂ} (ha : a ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn ((Set.range γ)ᶜ) a)) :
    ¬ Commons.Topology.Winding.HasArg (fun t : ℝ => γ (Circle.exp (2 * Real.pi * t)) - a) 0 := by
  intro harg
  obtain ⟨Λ, hΛinj, hΛexp⟩ := Work.HornSC.JC.exists_injective_lift hγ ha harg
  set L : Set ℂ := Set.range Λ with hL
  have hLcpt : IsCompact L := isCompact_range Λ.continuous
  have hLconn : IsConnected L := ⟨⟨Λ 1, ⟨1, rfl⟩⟩, isPreconnected_range Λ.continuous⟩
  obtain ⟨U, V, hUo, hVo, hUconn, hVconn, hUVdisj, hUb, hVunb, hUVcover⟩ :=
    Commons.Topology.Jordan.plane_separation Λ hΛinj
  have hUsub : U ⊆ Lᶜ := fun z hz => by rw [← hUVcover]; exact Or.inl hz
  have hVsub : V ⊆ Lᶜ := fun z hz => by rw [← hUVcover]; exact Or.inr hz
  have hnotU : ∀ z : ℂ, ¬ Bornology.IsBounded (connectedComponentIn Lᶜ z) → z ∉ U := by
    intro z hz hzU
    have hzLc : z ∈ Lᶜ := hUsub hzU
    have hsub : connectedComponentIn Lᶜ z ⊆ U ∨ connectedComponentIn Lᶜ z ⊆ V :=
      isPreconnected_connectedComponentIn.subset_or_subset hUo hVo hUVdisj
        (by rw [hUVcover]; exact connectedComponentIn_subset Lᶜ z)
    rcases hsub with hs | hs
    · exact hz (hUb.subset hs)
    · exact (Set.disjoint_left.mp hUVdisj) hzU (hs (mem_connectedComponentIn hzLc))
  have hmemV : ∀ z : ℂ, z ∉ L → ¬ Bornology.IsBounded (connectedComponentIn Lᶜ z) → z ∈ V := by
    intro z hzL hz
    have hzLc : z ∈ Lᶜ := hzL
    have hsub : connectedComponentIn Lᶜ z ⊆ U ∨ connectedComponentIn Lᶜ z ⊆ V :=
      isPreconnected_connectedComponentIn.subset_or_subset hUo hVo hUVdisj
        (by rw [hUVcover]; exact connectedComponentIn_subset Lᶜ z)
    rcases hsub with hs | hs
    · exact absurd (hUb.subset hs) hz
    · exact hs (mem_connectedComponentIn hzLc)
  -- the exponential translate vectors
  have hexp_shift : ∀ n : ℤ, Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I)) = 1 := by
    intro n
    exact Complex.exp_eq_one_iff.mpr ⟨n, by ring⟩
  have htwopi : (2 * Real.pi * Complex.I) ≠ 0 := by
    intro h
    have h1 := congrArg Complex.im h
    simp at h1
  -- the translates of the curve miss the curve
  have hcoset : ∀ n : ℤ, n ≠ 0 →
      Disjoint L (L + ({(n : ℂ) * (2 * Real.pi * Complex.I)} : Set ℂ)) := by
    intro n hn
    rw [Set.disjoint_left]
    rintro w hw1 hw2
    obtain ⟨z, rfl⟩ := hw1
    obtain ⟨x, hxL, c, hc, hxc⟩ := Set.mem_add.mp hw2
    obtain ⟨z', rfl⟩ := hxL
    rw [mem_singleton_iff] at hc
    subst hc
    have hexp_eq : Complex.exp (Λ z) = Complex.exp (Λ z' + (n : ℂ) * (2 * Real.pi * Complex.I)) := by
      rw [← hxc]
    rw [hΛexp z, Complex.exp_add, hΛexp z', hexp_shift n, mul_one] at hexp_eq
    have hγeq : γ z = γ z' := by
      simpa using congrArg (· + a) hexp_eq
    have hzz : z = z' := hγ hγeq
    rw [hzz] at hxc
    have hv0 : (n : ℂ) * (2 * Real.pi * Complex.I) = 0 := by
      have h : Λ z' + (n : ℂ) * (2 * Real.pi * Complex.I) = Λ z' + 0 := by
        rw [add_zero]; exact hxc
      exact add_left_cancel h
    exact hn (Int.cast_eq_zero.mp ((mul_eq_zero.mp hv0).resolve_right htwopi))
  -- every translate lies in the unbounded component
  have htrans : ∀ n : ℤ, n ≠ 0 → ∀ q ∈ L + ({(n : ℂ) * (2 * Real.pi * Complex.I)} : Set ℂ),
      q ∈ V := by
    intro n hn q hq
    have hqL : q ∉ L := fun hqL => (Set.disjoint_left.mp (hcoset n hn)) hqL hq
    have hyne : ((n : ℝ) * (2 * Real.pi)) ≠ 0 := by
      intro h
      rcases mul_eq_zero.mp h with h1 | h1
      · exact hn (Int.cast_eq_zero.mp h1)
      · exact absurd h1 (by positivity)
    have hv_eq : (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
        = (n : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
    have hdisj' : Disjoint L (L + ({(((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I} : Set ℂ)) := by
      rw [hv_eq]; exact hcoset n hn
    have hq' : q ∈ L + ({(((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I} : Set ℂ) := by
      rw [hv_eq]; exact hq
    exact hmemV q hqL (translate_subset_unbounded_of_im hLcpt hLconn hyne hdisj' hq')
  -- the preimages of the curve under `exp`
  have hexpset : ∀ z : ℂ, Complex.exp z ∈ (Set.range fun z : Circle => Complex.exp (Λ z)) ↔
      ∃ n : ℤ, z - (n : ℂ) * (2 * Real.pi * Complex.I) ∈ L := by
    intro z
    constructor
    · rintro ⟨z', hz'⟩
      obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp hz'.symm
      refine ⟨m, ?_⟩
      rw [hL]
      refine ⟨z', ?_⟩
      rw [hm]; ring
    · rintro ⟨n, hn⟩
      obtain ⟨z', hz'⟩ := hn
      refine ⟨z', ?_⟩
      have h1 : z = Λ z' + (n : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [hz']; ring
      rw [h1, Complex.exp_add, hexp_shift n, mul_one]
  have hU_avoid : ∀ z ∈ U, Complex.exp z ∉ (Set.range fun z : Circle => Complex.exp (Λ z)) := by
    intro z hzU hexpL
    obtain ⟨n, hn⟩ := (hexpset z).mp hexpL
    have hzmem : z ∈ L + ({(n : ℂ) * (2 * Real.pi * Complex.I)} : Set ℂ) := by
      refine Set.mem_add.mpr ⟨z - (n : ℂ) * (2 * Real.pi * Complex.I), hn,
        (n : ℂ) * (2 * Real.pi * Complex.I), mem_singleton _, by ring⟩
    by_cases hn0 : n = 0
    · subst hn0
      have hzL : z ∈ L := by
        obtain ⟨l, hl, c, hc, hlc⟩ := Set.mem_add.mp hzmem
        rw [mem_singleton_iff] at hc
        subst hc
        simp only [Int.cast_zero, zero_mul, add_zero] at hlc
        exact hlc ▸ hl
      exact (hUsub hzU) hzL
    · exact (Set.disjoint_left.mp hUVdisj) hzU (htrans n hn0 z hzmem)
  -- the vertical bounds on `U`
  obtain ⟨pmin, hpminL, hpmin⟩ := hLcpt.exists_isMinOn hLconn.nonempty Complex.continuous_re.continuousOn
  obtain ⟨pmax, hpmaxL, hpmax⟩ := hLcpt.exists_isMaxOn hLconn.nonempty Complex.continuous_re.continuousOn
  have hU_re_ge : ∀ z ∈ U, pmin.re ≤ z.re := by
    intro z hzU
    by_contra hcon
    push_neg at hcon
    exact hnotU z (Work.HornSC.JC.componentIn_unbounded_of_halfplane
      (Or.inr (Or.inl fun w hw => lt_of_lt_of_le hcon (hpmin hw)))) hzU
  have hU_re_le : ∀ z ∈ U, z.re ≤ pmax.re := by
    intro z hzU
    by_contra hcon
    push_neg at hcon
    exact hnotU z (Work.HornSC.JC.componentIn_unbounded_of_halfplane
      (Or.inl fun w hw => lt_of_le_of_lt (hpmax hw) hcon)) hzU
  have hexpU_bdd : Bornology.IsBounded (Complex.exp '' U) := by
    refine Bornology.IsBounded.subset
      (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := Real.exp pmax.re)) ?_
    rintro w ⟨z, hzU, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hU_re_le z hzU)
  have h0notexpU : (0 : ℂ) ∉ Complex.exp '' U := by
    rintro ⟨z, hzU, hz⟩
    exact Complex.exp_ne_zero z hz
  -- the second curve and its complementary components
  set γ' : C(Circle, ℂ) := ⟨fun z => γ z - a, by fun_prop⟩ with hγ'
  have hγ'inj : Function.Injective γ' := by
    intro z z' hzz
    apply hγ
    have h := hzz
    simp only [hγ', ContinuousMap.coe_mk] at h
    simpa using congrArg (· + a) h
  obtain ⟨U', V', hU'o, hV'o, hU'conn, hV'conn, hU'V'disj, hU'b, hV'unb, hU'V'cover⟩ :=
    Commons.Topology.Jordan.plane_separation γ' hγ'inj
  have hU'sub : U' ⊆ (Set.range γ')ᶜ := by
    rw [← hU'V'cover]; exact Set.subset_union_left
  have hV'sub : V' ⊆ (Set.range γ')ᶜ := by
    rw [← hU'V'cover]; exact Set.subset_union_right
  have hrange : Set.range γ' = Set.range (fun z : Circle => Complex.exp (Λ z)) := by
    ext w; constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, by simp only [hγ', ContinuousMap.coe_mk, hΛexp z]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by simp only [hγ', ContinuousMap.coe_mk, hΛexp z]⟩
  have h0W : (0 : ℂ) ∈ (Set.range γ')ᶜ := by
    rintro ⟨z, hz⟩
    have h1 : γ z = a := by
      have h := hz
      simp only [hγ', ContinuousMap.coe_mk] at h
      exact sub_eq_zero.mp h
    exact ha ⟨z, h1⟩
  have hWopen : IsOpen ((Set.range γ')ᶜ) := by
    rw [← hU'V'cover]; exact hU'o.union hV'o
  have h0W' : (0 : ℂ) ∈ (Set.range (fun z : Circle => Complex.exp (Λ z)))ᶜ := by
    rw [← hrange]; exact h0W
  set D : Set ℂ := connectedComponentIn ((Set.range γ')ᶜ) 0 with hD
  have hD0 : (0 : ℂ) ∈ D := mem_connectedComponentIn h0W
  have hDopen : IsOpen D := hWopen.connectedComponentIn
  have hDconn : IsConnected D := ⟨⟨0, hD0⟩, isPreconnected_connectedComponentIn⟩
  have hDsub : D ⊆ (Set.range γ')ᶜ := connectedComponentIn_subset _ 0
  have hDminus : IsConnected (D \ {0}) := Work.HornSC.JC.isConnected_diff_singleton hDopen hDconn hD0
  have hDcomp : D = U' ∨ D = V' := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset hU'o hV'o hU'V'disj
      (by rw [hU'V'cover]; exact hDsub) with h | h
    · left
      exact Subset.antisymm h (hU'conn.isPreconnected.subset_connectedComponentIn (h hD0) hU'sub)
    · right
      exact Subset.antisymm h (hV'conn.isPreconnected.subset_connectedComponentIn (h hD0) hV'sub)
  -- `D` is bounded, so it is the bounded component `U'`
  have hDbdd : Bornology.IsBounded D := by
    have hDC : D = connectedComponentIn ((Set.range γ)ᶜ) a + ({-a} : Set ℂ) := by
      have hD' : D = connectedComponentIn ((Set.range (fun z : Circle => Complex.exp (Λ z)))ᶜ) 0 := by
        rw [hD, hrange]
      rw [hD']
      apply Subset.antisymm
      · intro x hx
        refine Set.mem_add.mpr ⟨x + a, ?_, -a, mem_singleton _, by ring⟩
        have himg : IsPreconnected ((fun y : ℂ => y + a) ''
            connectedComponentIn ((Set.range (fun z : Circle => Complex.exp (Λ z)))ᶜ) 0) :=
          isPreconnected_connectedComponentIn.image (fun y : ℂ => y + a) (by fun_prop)
        have hsub : (fun y : ℂ => y + a) ''
            connectedComponentIn ((Set.range (fun z : Circle => Complex.exp (Λ z)))ᶜ) 0
            ⊆ (Set.range γ)ᶜ := by
          rintro y ⟨w, hw, rfl⟩
          have hw' := connectedComponentIn_subset _ 0 hw
          simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hw'
          simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
          intro z hz
          refine hw' z ?_
          rw [hΛexp z, hz]; ring
        exact himg.subset_connectedComponentIn ⟨0, mem_connectedComponentIn h0W', by ring⟩ hsub
          ⟨x, hx, rfl⟩
      · rintro x ⟨c, hc, d, hd, rfl⟩
        rw [mem_singleton_iff] at hd
        subst hd
        have himg : IsPreconnected
            ((fun y : ℂ => y - a) '' connectedComponentIn ((Set.range γ)ᶜ) a) :=
          isPreconnected_connectedComponentIn.image (fun y : ℂ => y - a) (by fun_prop)
        have hsub : (fun y : ℂ => y - a) '' connectedComponentIn ((Set.range γ)ᶜ) a ⊆
            (Set.range (fun z : Circle => Complex.exp (Λ z)))ᶜ := by
          rintro y ⟨w, hw, rfl⟩
          have hw' := connectedComponentIn_subset ((Set.range γ)ᶜ) a hw
          simp only [Set.mem_compl_iff, Set.mem_range, not_exists] at hw'
          simp only [Set.mem_compl_iff, Set.mem_range, not_exists]
          intro z hz
          refine hw' z ?_
          have h3 : γ z - a = w - a := by rw [← hΛexp z, hz]
          simpa using congrArg (· + a) h3
        exact himg.subset_connectedComponentIn
          ⟨a, mem_connectedComponentIn (by simpa using ha), by ring⟩ hsub ⟨c, hc, rfl⟩
    rw [hDC]
    exact hbdd.add (Set.finite_singleton (-a)).isBounded
  have hDeq : D = U' := by
    rcases hDcomp with h | h
    · exact h
    · exact absurd (h ▸ hDbdd) hV'unb
  -- `exp '' U` is open and closed inside the complement of `0`
  have hexpU_open : IsOpen (Complex.exp '' U) := Complex.isOpenMap_exp U hUo
  have hUcl : closure U ∩ Lᶜ = U := by
    obtain ⟨x, hxU⟩ := hUconn.nonempty
    have hUeq : U = connectedComponentIn Lᶜ x := by
      have h1 : U ⊆ connectedComponentIn Lᶜ x :=
        hUconn.isPreconnected.subset_connectedComponentIn hxU hUsub
      have h2 : connectedComponentIn Lᶜ x ⊆ U := by
        rcases isPreconnected_connectedComponentIn.subset_or_subset hUo hVo hUVdisj
          (by rw [hUVcover]; exact connectedComponentIn_subset Lᶜ x) with hs | hs
        · exact hs
        · exact absurd (hs (mem_connectedComponentIn (hUsub hxU)))
            ((Set.disjoint_left.mp hUVdisj) hxU)
      exact Subset.antisymm h1 h2
    rw [hUeq]; exact Work.HornSC.JC.closure_componentIn_inter x
  have hexpU_closed : closure (Complex.exp '' U) ∩ (Set.range γ')ᶜ ⊆ Complex.exp '' U := by
    rintro w ⟨hwcl, hwW⟩
    have hseq : ∀ n : ℕ, ∃ z ∈ U, dist (Complex.exp z) w < 1 / ((n : ℝ) + 1) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp hwcl (1 / ((n : ℝ) + 1)) hpos
      obtain ⟨z, hzU, rfl⟩ := hy
      exact ⟨z, hzU, by rwa [dist_comm] at hyd⟩
    choose z hzU hzdist using hseq
    obtain ⟨R, hR⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp hUb
    have hzbd : ∀ n, z n ∈ Metric.closedBall (0 : ℂ) R := fun n => hR (hzU n)
    obtain ⟨z₀, hz₀cc, φ, hφmono, hφtend⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq hzbd
    have hz₀cl : z₀ ∈ closure U :=
      isClosed_closure.mem_of_tendsto hφtend
        (Filter.Eventually.of_forall fun n => subset_closure (hzU (φ n)))
    have hlim1 : Tendsto (fun n => Complex.exp (z (φ n))) atTop (𝓝 (Complex.exp z₀)) :=
      Complex.continuous_exp.continuousAt.tendsto.comp hφtend
    have hlim2 : Tendsto (fun n => Complex.exp (z (φ n))) atTop (𝓝 w) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun n => dist_nonneg) (fun n => le_of_lt (hzdist (φ n))) ?_
      have hmono : ∀ n : ℕ, n ≤ φ n := fun n => hφmono.id_le n
      have hle : ∀ n : ℕ, 1 / (((φ n : ℕ) : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) := by
        intro n
        have hn : (n : ℝ) ≤ (φ n : ℝ) := by exact_mod_cast hmono n
        refine one_div_le_one_div_of_le (by positivity) ?_
        linarith
      refine squeeze_zero (fun n => by positivity) hle ?_
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds
      exact tendsto_const_nhds.div_atTop h1
    have hexpz₀ : Complex.exp z₀ = w := tendsto_nhds_unique hlim1 hlim2
    have hz₀notL : z₀ ∉ L := by
      intro hz₀L
      obtain ⟨z', rfl⟩ := hz₀L
      exact hwW ⟨z', by simp only [hγ', ContinuousMap.coe_mk, ← hexpz₀, hΛexp z']⟩
    have hz₀U : z₀ ∈ U := by
      have h : z₀ ∈ closure U ∩ Lᶜ := ⟨hz₀cl, hz₀notL⟩
      rwa [hUcl] at h
    exact ⟨z₀, hz₀U, hexpz₀⟩
  -- `exp '' U` lies in `D \ {0}`
  have hsub1 : Complex.exp '' U ⊆ (Set.range γ')ᶜ := by
    rintro w ⟨z, hzU, hz⟩
    rw [← hz, hrange]
    exact hU_avoid z hzU
  have hexpU_sub : Complex.exp '' U ⊆ D \ {0} := by
    have hconn : IsPreconnected (Complex.exp '' U) :=
      hUconn.isPreconnected.image Complex.exp (by fun_prop)
    rcases hconn.subset_or_subset hU'o hV'o hU'V'disj
      (by rw [hU'V'cover]; exact hsub1) with hs | hs
    · refine fun w hw => ⟨?_, ?_⟩
      · rw [hDeq]; exact hs hw
      · intro hw0; exact h0notexpU (hw0 ▸ hw)
    · exfalso
      have hcover : V' ⊆ Complex.exp '' U ∪ (closure (Complex.exp '' U))ᶜ := by
        intro x hx
        by_cases hxU : x ∈ Complex.exp '' U
        · exact Or.inl hxU
        · refine Or.inr fun hxcl => hxU (hexpU_closed ⟨hxcl, hV'sub hx⟩)
      rcases hV'conn.isPreconnected.subset_or_subset hexpU_open isClosed_closure.isOpen_compl
        ((disjoint_compl_right).mono_left subset_closure) hcover with h | h
      · exact hV'unb (hexpU_bdd.subset h)
      · obtain ⟨w, hw⟩ := hUconn.nonempty.image Complex.exp
        exact h (hs hw) (subset_closure hw)
  -- conclusion: `exp '' U = D \ {0}`
  have hWstar : (Set.range γ')ᶜ \ {0} = (D \ {0}) ∪ V' := by
    have h1 : (Set.range γ')ᶜ = D ∪ V' := by
      rw [← hU'V'cover, ← hDeq]
    rw [h1]
    ext x; constructor
    · rintro ⟨hx | hx, hx0⟩
      · exact Or.inl ⟨hx, hx0⟩
      · exact Or.inr hx
    · rintro (⟨hx, hx0⟩ | hx)
      · exact ⟨Or.inl hx, hx0⟩
      · refine ⟨Or.inr hx, ?_⟩
        intro h0
        rw [h0] at hx
        exact (Set.disjoint_left.mp hU'V'disj) (by rw [← hDeq]; exact hD0) hx
  have hexpU_eq : Complex.exp '' U = D \ {0} := by
    have hcover : D \ {0} ⊆ Complex.exp '' U ∪ (closure (Complex.exp '' U))ᶜ := by
      intro x hx
      by_cases hxU : x ∈ Complex.exp '' U
      · exact Or.inl hxU
      · refine Or.inr fun hxcl => hxU (hexpU_closed ⟨hxcl, hDsub hx.1⟩)
    rcases hDminus.isPreconnected.subset_or_subset hexpU_open isClosed_closure.isOpen_compl
      ((disjoint_compl_right).mono_left subset_closure) hcover with h | h
    · exact Subset.antisymm hexpU_sub h
    · obtain ⟨w, hw⟩ := hUconn.nonempty.image Complex.exp
      exact absurd (subset_closure hw) (h (hexpU_sub hw))
  -- the final contradiction
  obtain ⟨ρ, hρpos, hρsub⟩ : ∃ ρ > 0, Metric.ball (0 : ℂ) ρ ⊆ D :=
    Metric.isOpen_iff.mp hDopen 0 hD0
  set ε : ℝ := min ρ (Real.exp pmin.re) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hmin : min ρ (Real.exp pmin.re) > 0 := lt_min hρpos (Real.exp_pos _)
  have hερ : ε < ρ := by
    rw [hε]
    have h1 := min_le_left ρ (Real.exp pmin.re)
    linarith
  have hεexp : ε < Real.exp pmin.re := by
    rw [hε]
    have h1 := min_le_right ρ (Real.exp pmin.re)
    have h2 := Real.exp_pos pmin.re
    linarith
  have hεD : (ε : ℂ) ∈ D \ {0} := by
    refine ⟨?_, ?_⟩
    · exact hρsub (by
        rw [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos]
        exact hερ)
    · simp only [Set.mem_singleton_iff]
      intro h
      have h1 : ε = 0 := by exact_mod_cast h
      exact absurd h1 (ne_of_gt hεpos)
  have hmem : (ε : ℂ) ∈ Complex.exp '' U := by rw [hexpU_eq]; exact hεD
  obtain ⟨z, hzU, hzε⟩ := hmem
  have hzre : z.re = Real.log ε := by
    have h1 : Real.exp z.re = ε := by
      have := congrArg (fun w : ℂ => ‖w‖) hzε
      rw [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεpos] at this
      exact this
    calc z.re = Real.log (Real.exp z.re) := (Real.log_exp z.re).symm
      _ = Real.log ε := by rw [h1]
  have hge := hU_re_ge z hzU
  rw [hzre] at hge
  exact absurd hge (not_le.mpr (by
    have := Real.log_lt_log hεpos hεexp
    rwa [Real.log_exp] at this))

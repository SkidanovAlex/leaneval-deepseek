import Mathlib
import Submission.Work.WilE2.Ebc.Defs

set_option autoImplicit false
noncomputable section

open Classical
open scoped Topology
open Filter

namespace Work.WilE2.Ebc

open Work.WilE2

/-! ### A decreasing sequence of positive reals below every threshold -/

private noncomputable def tshrink {P : ℝ → Prop}
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε) (δ : ℝ) : ℝ :=
  if hδ : 0 < δ then Classical.choose (h δ hδ) else δ

private lemma tshrink_pos {P : ℝ → Prop}
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε) {δ : ℝ} (hδ : 0 < δ) :
    0 < tshrink h δ := by
  unfold tshrink
  rw [dif_pos hδ]
  exact (Classical.choose_spec (h δ hδ)).1

private lemma tshrink_lt {P : ℝ → Prop}
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε) {δ : ℝ} (hδ : 0 < δ) :
    tshrink h δ < δ := by
  unfold tshrink
  rw [dif_pos hδ]
  exact (Classical.choose_spec (h δ hδ)).2.1

private lemma tshrink_P {P : ℝ → Prop}
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε) {δ : ℝ} (hδ : 0 < δ) :
    P (tshrink h δ) := by
  unfold tshrink
  rw [dif_pos hδ]
  exact (Classical.choose_spec (h δ hδ)).2.2

private noncomputable def tseq {P : ℝ → Prop}
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε) : ℕ → ℝ
  | 0 => tshrink h 1
  | n + 1 => tshrink h (min (tseq h n) (1 / ((n : ℝ) + 1)))

theorem ts_exists_strictAnti_seq {P : ℝ → Prop}
    (h : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ P ε) :
    ∃ u : ℕ → ℝ, (∀ n, 0 < u n) ∧ (∀ n, u (n+1) < u n) ∧ (∀ n, P (u n)) ∧
      (∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ n, M ≤ n → u n < η) := by
  classical
  have hpos : ∀ n, 0 < tseq h n := by
    intro n
    induction n with
    | zero => exact tshrink_pos h one_pos
    | succ k ih =>
        show 0 < tshrink h (min (tseq h k) (1 / ((k : ℝ) + 1)))
        exact tshrink_pos h (lt_min ih (by positivity))
  have hP : ∀ n, P (tseq h n) := by
    intro n
    induction n with
    | zero => exact tshrink_P h one_pos
    | succ k _ =>
        show P (tshrink h (min (tseq h k) (1 / ((k : ℝ) + 1))))
        exact tshrink_P h (lt_min (hpos k) (by positivity))
  have hlt : ∀ n, tseq h (n+1) < tseq h n := by
    intro n
    have hmin : 0 < min (tseq h n) (1 / ((n : ℝ) + 1)) :=
      lt_min (hpos n) (by positivity)
    calc tseq h (n+1) = tshrink h (min (tseq h n) (1 / ((n : ℝ) + 1))) := rfl
      _ < min (tseq h n) (1 / ((n : ℝ) + 1)) := tshrink_lt h hmin
      _ ≤ tseq h n := min_le_left _ _
  have hbound : ∀ n, tseq h (n+1) < 1 / ((n : ℝ) + 1) := by
    intro n
    have hmin : 0 < min (tseq h n) (1 / ((n : ℝ) + 1)) :=
      lt_min (hpos n) (by positivity)
    calc tseq h (n+1) = tshrink h (min (tseq h n) (1 / ((n : ℝ) + 1))) := rfl
      _ < min (tseq h n) (1 / ((n : ℝ) + 1)) := tshrink_lt h hmin
      _ ≤ 1 / ((n : ℝ) + 1) := min_le_right _ _
  refine ⟨tseq h, hpos, hlt, hP, ?_⟩
  intro η hη
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / η)
  have hNpos : (0 : ℝ) < (N : ℝ) := lt_trans (div_pos one_pos hη) hN
  have hNlt : 1 / (N : ℝ) < η := by
    rw [div_lt_iff₀ hNpos]
    have h1 : (1 : ℝ) < (N : ℝ) * η := (div_lt_iff₀ hη).mp hN
    linarith [h1]
  refine ⟨N, fun n hn => ?_⟩
  have hNge1 : 1 ≤ N := by
    have hN0 : (0 : ℕ) < N := Nat.cast_pos.mp hNpos
    omega
  have hn0 : n ≠ 0 := by omega
  have hb : tseq h n < 1 / (n : ℝ) := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    rw [hm]
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using hbound m
  have hle : 1 / (n : ℝ) ≤ 1 / (N : ℝ) :=
    one_div_le_one_div_of_le hNpos (by exact_mod_cast hn)
  linarith [hb, hle, hNlt]

/-! ### Nested intersection of compact continua -/

theorem ts_preconnected_iInter {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : ℕ → Set X} (hanti : Antitone K) (hKc : ∀ n, IsCompact (K n))
    (hKp : ∀ n, IsPreconnected (K n)) : IsPreconnected (⋂ n, K n) := by
  intro u v hu hv huv hAu hAv
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  set A : Set X := ⋂ n, K n with hAdef
  have hAuv : A ⊆ u ∪ v := huv
  have hAc : IsClosed A := by
    rw [hAdef]
    exact isClosed_iInter fun n => (hKc n).isClosed
  have hdisj : A ∩ u ∩ v = ∅ := by
    rw [Set.inter_assoc]
    exact hcon
  have hBu : A ∩ u = A ∩ vᶜ := by
    ext z
    refine ⟨fun hz => ⟨hz.1, fun hzv => ?_⟩, fun hz => ?_⟩
    · have hmem : z ∈ A ∩ u ∩ v := ⟨hz, hzv⟩
      rw [hdisj] at hmem
      exact hmem
    · rcases hAuv hz.1 with h | h
      · exact ⟨hz.1, h⟩
      · exact absurd h hz.2
  have hCv : A ∩ v = A ∩ uᶜ := by
    ext z
    refine ⟨fun hz => ⟨hz.1, fun hzu => ?_⟩, fun hz => ?_⟩
    · have hmem : z ∈ A ∩ u ∩ v := ⟨⟨hz.1, hzu⟩, hz.2⟩
      rw [hdisj] at hmem
      exact hmem
    · rcases hAuv hz.1 with h | h
      · exact absurd h hz.2
      · exact ⟨hz.1, h⟩
  have hBc : IsClosed (A ∩ u) := by rw [hBu]; exact hAc.inter (isClosed_compl_iff.mpr hv)
  have hCc : IsClosed (A ∩ v) := by rw [hCv]; exact hAc.inter (isClosed_compl_iff.mpr hu)
  have hBcpt : IsCompact (A ∩ u) :=
    (hKc 0).of_isClosed_subset hBc (fun z hz => Set.iInter_subset K 0 hz.1)
  have hCcpt : IsCompact (A ∩ v) :=
    (hKc 0).of_isClosed_subset hCc (fun z hz => Set.iInter_subset K 0 hz.1)
  have hdisjBC : Disjoint (A ∩ u) (A ∩ v) :=
    Set.disjoint_left.mpr (fun z hz1 hz2 => by
      have hmem : z ∈ A ∩ u ∩ v := ⟨hz1, hz2.2⟩
      rw [hdisj] at hmem
      exact hmem)
  obtain ⟨U, V, hUo, hVo, hBU, hCV, hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact hBcpt hCcpt hdisjBC
  have hUcV : IsClosed ((U ∪ V)ᶜ) := (hUo.union hVo).isClosed_compl
  have hAUV : A ⊆ U ∪ V := by
    intro z hz
    rcases hAuv hz with h | h
    · exact Or.inl (hBU ⟨hz, h⟩)
    · exact Or.inr (hCV ⟨hz, h⟩)
  have hempty : ∃ n, K n ∩ (U ∪ V)ᶜ = ∅ := by
    by_contra h
    push Not at h
    have hdir : Directed (fun s t : Set X => s ⊇ t) (fun n => K n ∩ (U ∪ V)ᶜ) := by
      intro i j
      exact ⟨max i j, Set.inter_subset_inter (hanti (le_max_left i j)) (le_refl _),
        Set.inter_subset_inter (hanti (le_max_right i j)) (le_refl _)⟩
    have hne : (⋂ n, K n ∩ (U ∪ V)ᶜ).Nonempty :=
      IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
        (fun n => K n ∩ (U ∪ V)ᶜ) hdir (fun n => h n)
        (fun n => (hKc n).inter_right hUcV)
        (fun n => (hKc n).isClosed.inter hUcV)
    obtain ⟨z, hz⟩ := hne
    have hz1 : z ∈ A := Set.mem_iInter.mpr (fun n => (Set.mem_iInter.mp hz n).1)
    have hz2 : z ∈ (U ∪ V)ᶜ := (Set.mem_iInter.mp hz 0).2
    exact hz2 (hAUV hz1)
  obtain ⟨n, hn⟩ := hempty
  have hKnUV : K n ⊆ U ∪ V := fun z hz => by
    by_contra hz'
    have hmem : z ∈ K n ∩ (U ∪ V)ᶜ := ⟨hz, hz'⟩
    rw [hn] at hmem
    exact hmem
  obtain ⟨z0, hz0⟩ := hAu
  obtain ⟨z1, hz1⟩ := hAv
  have hbU : (K n ∩ U).Nonempty := ⟨z0, Set.iInter_subset K n hz0.1, hBU hz0⟩
  have hcV : (K n ∩ V).Nonempty := ⟨z1, Set.iInter_subset K n hz1.1, hCV hz1⟩
  obtain ⟨z, hzK, hzU, hzV⟩ := hKp n U V hUo hVo hKnUV hbU hcV
  exact hUV.le_bot ⟨hzU, hzV⟩

/-! ### Elementary properties of the tube functions -/

theorem continuous_tubeFun {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (hφc : Continuous φ) (ρ ε : ℝ) :
    Continuous (tubeFun φ ρ ε) := by
  unfold tubeFun
  exact hφc.add (continuous_const.mul
    ((continuous_finsetSum _ (fun i _ => (continuous_apply i).pow 2)).sub continuous_const))

theorem isClosed_tubeSet {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (hφc : Continuous φ) (ρ ε : ℝ) :
    IsClosed (tubeSet φ ρ ε) := by
  have h : tubeSet φ ρ ε = (tubeFun φ ρ ε) ⁻¹' (Set.Iic 0) := rfl
  rw [h]
  exact isClosed_Iic.preimage (continuous_tubeFun φ hφc ρ ε)

theorem tubeSet_subset_eball {k : ℕ} {φ : (Fin k → ℝ) → ℝ} {ρ ε : ℝ} (hε : 0 < ε)
    (hφnn : ∀ y, 0 ≤ φ y) : tubeSet φ ρ ε ⊆ eball k ρ := by
  intro y hy
  have hy' : φ y + ε * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ 0 := hy
  show ∑ i, (y i) ^ 2 ≤ ρ ^ 2
  have h1 : ε * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ 0 := by have := hφnn y; linarith
  have h2 : ∑ i, (y i) ^ 2 - ρ ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [h1, hε, h]
  linarith

theorem mem_tubeSet_of_zero {k : ℕ} {φ : (Fin k → ℝ) → ℝ} {ρ ε : ℝ} {y : Fin k → ℝ}
    (hZ : φ y = 0) (hb : ∑ i, (y i) ^ 2 ≤ ρ ^ 2) (hε : 0 ≤ ε) : y ∈ tubeSet φ ρ ε := by
  show tubeFun φ ρ ε y ≤ 0
  have h2 : ∑ i, (y i) ^ 2 - ρ ^ 2 ≤ 0 := by linarith
  have h3 : ε * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hε h2
  unfold tubeFun
  rw [hZ]
  linarith

theorem tubeSet_mono {k : ℕ} {φ : (Fin k → ℝ) → ℝ} (hφnn : ∀ y, 0 ≤ φ y) {ρ ε ε' : ℝ}
    (h0 : 0 < ε) (hle : ε ≤ ε') : tubeSet φ ρ ε ⊆ tubeSet φ ρ ε' := by
  intro y hy
  have hy' : φ y + ε * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ 0 := hy
  show φ y + ε' * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ 0
  have h1 : ε * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ 0 := by have := hφnn y; linarith
  have h2 : ∑ i, (y i) ^ 2 - ρ ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    nlinarith [h1, h0, h]
  have h3 : ε' * (∑ i, (y i) ^ 2 - ρ ^ 2) ≤ ε * (∑ i, (y i) ^ 2 - ρ ^ 2) :=
    mul_le_mul_of_nonpos_right hle h2
  linarith

/-- The connected component of a point in a closed set is closed. -/
theorem isClosed_connectedComponentIn_of_isClosed {X : Type*} [TopologicalSpace X] {F : Set X}
    (hF : IsClosed F) (x : X) : IsClosed (connectedComponentIn F x) := by
  by_cases hx : x ∈ F
  · have hpre : IsPreconnected (closure (connectedComponentIn F x)) :=
      isPreconnected_connectedComponentIn.closure
    have hsub : closure (connectedComponentIn F x) ⊆ F := by
      calc closure (connectedComponentIn F x) ⊆ closure F :=
            closure_mono (connectedComponentIn_subset F x)
        _ = F := hF.closure_eq
    have hxcl : x ∈ closure (connectedComponentIn F x) :=
      subset_closure (mem_connectedComponentIn hx)
    have heq : closure (connectedComponentIn F x) = connectedComponentIn F x :=
      le_antisymm (hpre.subset_connectedComponentIn hxcl hsub) subset_closure
    rw [← heq]
    exact isClosed_closure
  · rw [connectedComponentIn_eq_empty hx]
    exact isClosed_empty

/-! ### The main statement -/

theorem tube_separation {k : ℕ} (φ : (Fin k → ℝ) → ℝ) (hφc : Continuous φ)
    (hφnn : ∀ x, 0 ≤ φ x) (ρ : ℝ) {N : ℕ} (x : Fin N → Fin k → ℝ)
    (hxZ : ∀ i, φ (x i) = 0) (hxball : ∀ i, ∑ j, (x i j) ^ 2 ≤ ρ ^ 2)
    (hsep : ∀ i j, i ≠ j →
      connectedComponentIn ({y : Fin k → ℝ | φ y = 0} ∩ eball k ρ) (x i)
        ≠ connectedComponentIn ({y : Fin k → ℝ | φ y = 0} ∩ eball k ρ) (x j)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j, i ≠ j →
      x j ∉ connectedComponentIn (tubeSet φ ρ ε) (x i) := by
  classical
  -- The per-pair statement.
  have key : ∀ i j : Fin N, i ≠ j → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < ε → ε < δ → x j ∉ connectedComponentIn (tubeSet φ ρ ε) (x i) := by
    intro i j hij
    by_contra hcon
    push Not at hcon
    -- An antitone family of compact continua, all containing `x i` and `x j`.
    obtain ⟨u, hu_pos, hu_dec, hu_mem, hu_small⟩ :=
      ts_exists_strictAnti_seq
        (P := fun ε : ℝ => x j ∈ connectedComponentIn (tubeSet φ ρ ε) (x i)) hcon
    let K : ℕ → Set (Fin k → ℝ) := fun n => connectedComponentIn (tubeSet φ ρ (u n)) (x i)
    have hu_anti : Antitone u := antitone_nat_of_succ_le (fun n => le_of_lt (hu_dec n))
    have hanti : Antitone K := by
      intro a b hab z hz
      have hsub : tubeSet φ ρ (u b) ⊆ tubeSet φ ρ (u a) :=
        tubeSet_mono hφnn (hu_pos b) (hu_anti hab)
      exact connectedComponentIn_mono (x i) hsub hz
    have hKc : ∀ n, IsCompact (K n) := by
      intro n
      exact (isCompact_eball k ρ).of_isClosed_subset
        (isClosed_connectedComponentIn_of_isClosed (isClosed_tubeSet φ hφc ρ (u n)) (x i))
        (subset_trans (connectedComponentIn_subset _ _)
          (tubeSet_subset_eball (hu_pos n) hφnn))
    have hKp : ∀ n, IsPreconnected (K n) := fun _ => isPreconnected_connectedComponentIn
    have hpre : IsPreconnected (⋂ n, K n) := ts_preconnected_iInter hanti hKc hKp
    have hxi : x i ∈ ⋂ n, K n := by
      refine Set.mem_iInter.mpr (fun n => ?_)
      exact mem_connectedComponentIn
        (mem_tubeSet_of_zero (hxZ i) (hxball i) (le_of_lt (hu_pos n)))
    have hxj : x j ∈ ⋂ n, K n := by
      refine Set.mem_iInter.mpr (fun n => ?_)
      exact hu_mem n
    -- The limit lies in the zero set.
    have hsubZ : (⋂ n, K n) ⊆ {y : Fin k → ℝ | φ y = 0} ∩ eball k ρ := by
      intro z hz
      have hzK : ∀ n, z ∈ K n := fun n => Set.mem_iInter.mp hz n
      have hztube : ∀ n, z ∈ tubeSet φ ρ (u n) := fun n =>
        connectedComponentIn_subset _ _ (hzK n)
      have hzball : z ∈ eball k ρ := tubeSet_subset_eball (hu_pos 0) hφnn (hztube 0)
      have hS : ∑ l, (z l) ^ 2 ≤ ρ ^ 2 := hzball
      have hineq : ∀ n, φ z ≤ u n * (ρ ^ 2 - ∑ l, (z l) ^ 2) := by
        intro n
        have h' : φ z + u n * (∑ l, (z l) ^ 2 - ρ ^ 2) ≤ 0 := hztube n
        nlinarith [h']
      have hphi : φ z = 0 := by
        refine le_antisymm ?_ (hφnn z)
        by_contra hlt
        push Not at hlt
        set c : ℝ := ρ ^ 2 - ∑ l, (z l) ^ 2 + 1 with hc
        have hcpos : 0 < c := by rw [hc]; linarith
        obtain ⟨M, hM⟩ := hu_small (φ z / c) (div_pos hlt hcpos)
        have hMM : u M * c < φ z := by
          have h1 : u M < φ z / c := hM M (le_refl M)
          rwa [lt_div_iff₀ hcpos] at h1
        have h4 : u M * (ρ ^ 2 - ∑ l, (z l) ^ 2) ≤ u M * c :=
          mul_le_mul_of_nonneg_left (by rw [hc]; linarith) (le_of_lt (hu_pos M))
        linarith [hineq M, hMM, h4]
      exact ⟨hphi, hzball⟩
    have hcc : (⋂ n, K n) ⊆
        connectedComponentIn ({y : Fin k → ℝ | φ y = 0} ∩ eball k ρ) (x i) :=
      hpre.subset_connectedComponentIn hxi hsubZ
    exact hsep i j hij (connectedComponentIn_eq (hcc hxj))
  -- Combine over the finitely many pairs.
  by_cases hN : N ≤ 1
  · refine ⟨1, one_pos, fun ε hε _ i j hij => ?_⟩
    have hij' : i = j := by
      apply Fin.ext
      have hi := i.isLt
      have hj := j.isLt
      omega
    exact absurd hij' hij
  · have hN2 : 0 < N := by omega
    let i0 : Fin N := ⟨0, hN2⟩
    have key' : ∀ i j : Fin N, ∃ δ : ℝ, 0 < δ ∧
        ∀ ε : ℝ, 0 < ε → ε < δ → i ≠ j →
          x j ∉ connectedComponentIn (tubeSet φ ρ ε) (x i) := by
      intro i j
      by_cases h : i = j
      · exact ⟨1, one_pos, fun ε hε hlt hij' => absurd h hij'⟩
      · exact ⟨Classical.choose (key i j h), (Classical.choose_spec (key i j h)).1,
          fun ε hε hlt _ => (Classical.choose_spec (key i j h)).2 ε hε hlt⟩
    let δ : Fin N → Fin N → ℝ := fun i j => Classical.choose (key' i j)
    have hδpos : ∀ i j, 0 < δ i j := fun i j => (Classical.choose_spec (key' i j)).1
    have hδprop : ∀ i j, i ≠ j → ∀ ε : ℝ, 0 < ε → ε < δ i j →
        x j ∉ connectedComponentIn (tubeSet φ ρ ε) (x i) :=
      fun i j h ε hε hlt => (Classical.choose_spec (key' i j)).2 ε hε hlt h
    let T : Finset ℝ :=
      Finset.univ.biUnion (fun i : Fin N => Finset.univ.image (fun j : Fin N => δ i j))
    have hTne : T.Nonempty := by
      refine ⟨δ i0 i0, ?_⟩
      show δ i0 i0 ∈ Finset.univ.biUnion
        (fun i : Fin N => Finset.univ.image (fun j : Fin N => δ i j))
      exact Finset.mem_biUnion.mpr
        ⟨i0, Finset.mem_univ _, Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩⟩
    refine ⟨T.min' hTne, ?_, ?_⟩
    · have hmemT := Finset.min'_mem T hTne
      rcases Finset.mem_biUnion.mp hmemT with ⟨i, -, hi⟩
      rcases Finset.mem_image.mp hi with ⟨j, -, hj⟩
      rw [← hj]
      exact hδpos i j
    · intro ε hε hε0 i j hij
      have hmem : δ i j ∈ T := by
        show δ i j ∈ Finset.univ.biUnion
          (fun i : Fin N => Finset.univ.image (fun j : Fin N => δ i j))
        exact Finset.mem_biUnion.mpr
          ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩
      have hle : T.min' hTne ≤ δ i j := Finset.min'_le T (δ i j) hmem
      exact hδprop i j hij ε hε (lt_of_lt_of_le hε0 hle)

end Work.WilE2.Ebc

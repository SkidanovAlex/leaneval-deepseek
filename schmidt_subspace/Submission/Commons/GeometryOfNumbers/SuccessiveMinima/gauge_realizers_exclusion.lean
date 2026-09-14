import Mathlib

namespace Commons.GeometryOfNumbers.SuccessiveMinima

open MeasureTheory Set
open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

/-! ### Helper lemmas (gauge of a symmetric convex body vs. scaled copies, finiteness of
lattice points with bounded gauge, existence of a lattice point outside a proper subspace) -/

/-- **Realizers of the successive minima with the strong interior-exclusion property.**

Let `K ⊆ ℝ^N` be a closed, bounded, convex, symmetric set with nonempty interior (so `0 ∈ K`
is an interior point and `gauge K` is a genuine norm-like functional).  Write, for `ℓ : ℕ`,
`λ ℓ := sInf {t > 0 | ∃ v : Fin ℓ → (Fin N → ℤ), LinearIndependent ℝ (fun a => (v a : ℝ^N)) ∧
∀ a, (v a : ℝ^N) ∈ t • K}` (the `ℓ`-th successive minimum of `K` with respect to the lattice
`ℤ^N`).

Then there is one `ℝ`-independent family `v : Fin N → (Fin N → ℤ)` of lattice vectors which
realizes all the successive minima simultaneously (`gauge K (v i) ≤ λ (i+1)`) and satisfies the
**strong interior exclusion property**: every lattice point `y` with `gauge K y < λ ℓ` lies in
the span of the first `ℓ - 1` realizers.

Templates: `Commons.Lattice.SuccessiveMinima.exact_realization` and
`Commons.Lattice.SuccessiveMinima.interior_exclusion` prove exactly this in the normed-lattice
setting (`‖·‖` instead of `gauge K`, `successiveMinimum L i` instead of the inlined `λ`); the
proof is norm-agnostic apart from
* `{y : Fin N → ℤ | gauge K y ≤ R}` is finite for every `R` (boundedness of `K` plus
  discreteness of `ℤ^N`),
* `gauge K x ≤ t ↔ x ∈ t • K` and `gauge K x < t ↔ x ∈ t • interior K` for `t ≥ 0`
  (`setOfPred_gauge_le_eq`, `setOfPred_gauge_lt_eq` in `Mathlib.Analysis.Convex.Gauge`),
* monotonicity of `λ` in `ℓ`, and `λ ℓ ≤ r` whenever `r • K` contains `ℓ` independent lattice
  vectors (`csInf_le`). -/
lemma smul_subset_smul_of_le_of_mem_zero {N : ℕ} {K : Set (Fin N → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin N → ℝ) ∈ K)
    {s s' : ℝ} (hs : 0 ≤ s) (hss : s ≤ s') : s • K ⊆ s' • K := by
  rintro x ⟨y, hy, rfl⟩
  rcases eq_or_lt_of_le hs with h | hspos
  · subst h
    simp only [zero_smul]
    exact ⟨0, h0, by simp⟩
  · have hs'pos : 0 < s' := lt_of_lt_of_le hspos hss
    refine ⟨(s / s') • y, hconv.smul_mem_of_zero_mem h0 hy
      ⟨div_nonneg hs hs'pos.le, (div_le_one hs'pos).mpr hss⟩, ?_⟩
    show s' • ((s / s') • y) = s • y
    rw [smul_smul, mul_div_cancel₀ s hs'pos.ne']

lemma finite_int_points_gauge_le_local {N : ℕ} {K : Set (Fin N → ℝ)}
    (hconv : Convex ℝ K) (h0 : (0 : Fin N → ℝ) ∈ interior K) (hbdd : Bornology.IsBounded K)
    (c : ℝ) : {z : Fin N → ℤ | gauge K (fun k => (z k : ℝ)) ≤ c}.Finite := by
  rcases lt_or_ge c 0 with hc | hc
  · have hempty : {z : Fin N → ℤ | gauge K (fun k => (z k : ℝ)) ≤ c} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      simp only [Set.mem_ofPred_eq] at hz
      have hnn := gauge_nonneg (s := K) (fun k => (z k : ℝ))
      linarith
    rw [hempty]
    exact Set.finite_empty
  · have h0K : (0 : Fin N → ℝ) ∈ K := interior_subset h0
    have habs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hbdd
    have hset : {z : Fin N → ℤ | gauge K (fun k => (z k : ℝ)) ≤ c} ⊆
        {z : Fin N → ℤ | ∀ k, (z k) ∈ ({n : ℤ | |(n:ℝ)| ≤ (c + 1) * M} : Set ℤ)} := by
      intro z hz
      have hzc : gauge K (fun k => (z k : ℝ)) ≤ c := hz
      have hc1 : 0 < c + 1 := by linarith
      have hmem : (fun k => (z k : ℝ)) ∈ ⋂ (r : ℝ), ⋂ (_ : c < r), r • K := by
        rw [← setOfPred_gauge_le_eq hconv h0K habs hc]
        exact hzc
      have hmem' : (fun k => (z k : ℝ)) ∈ (c+1) • K := by
        simp only [Set.mem_iInter] at hmem
        exact hmem (c+1) (by linarith)
      obtain ⟨y, hyK, hy⟩ := hmem'
      intro k
      simp only [Set.mem_ofPred_eq]
      have hk : (z k : ℝ) = (c+1) * y k := by
        have h := congr_fun hy k
        simp only [Pi.smul_apply, smul_eq_mul] at h
        exact h.symm
      calc |(z k : ℝ)| = (c+1) * |y k| := by rw [hk, abs_mul, abs_of_pos hc1]
        _ ≤ (c+1) * M := by
            refine mul_le_mul_of_nonneg_left (le_trans ?_ (hM y hyK)) hc1.le
            simpa using norm_le_pi_norm y k
    refine (Set.Finite.pi' (fun k => ?_)).subset hset
    refine (Set.finite_Icc ⌊-((c+1)*M)⌋ ⌈(c+1)*M⌉).subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    obtain ⟨hn1, hn2⟩ := abs_le.mp hn
    simp only [Set.mem_Icc]
    exact ⟨Int.floor_le_iff.mpr (by linarith), Int.le_ceil_iff.mpr (by linarith)⟩

lemma exists_int_vector_notMem {N : ℕ} {W : Submodule ℝ (Fin N → ℝ)} (hW : W ≠ ⊤) :
    ∃ z : Fin N → ℤ, (fun k => (z k : ℝ)) ∉ W := by
  by_contra h
  push Not at h
  apply hW
  have hspan : Submodule.span ℝ (Set.range (Pi.basisFun ℝ (Fin N))) =
      (⊤ : Submodule ℝ (Fin N → ℝ)) := (Pi.basisFun ℝ (Fin N)).span_eq
  refine le_antisymm le_top ?_
  rw [← hspan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨a, rfl⟩
  have hb : (Pi.basisFun ℝ (Fin N)) a =
      (fun k => ((Pi.single a (1:ℤ) : Fin N → ℤ) k : ℝ)) := by
    funext k
    rw [Pi.basisFun_apply]
    by_cases hk : k = a
    · subst hk; simp
    · rw [Pi.single_eq_of_ne (h := hk), Pi.single_eq_of_ne (h := hk)]
      simp
  rw [hb]
  exact h (Pi.single a (1:ℤ))


theorem gauge_realizers_exclusion (N : ℕ) (K : Set (Fin N → ℝ))
    (hconv : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) (hclosed : IsClosed K)
    (hbdd : Bornology.IsBounded K) (hint : (interior K).Nonempty) :
    ∃ v : Fin N → (Fin N → ℤ),
      LinearIndependent ℝ (fun i => fun k => (v i k : ℝ)) ∧
      (∀ i : Fin N, gauge K (fun k => (v i k : ℝ)) ≤
        sInf {t : ℝ | 0 < t ∧ ∃ w : Fin (i.val + 1) → (Fin N → ℤ),
          LinearIndependent ℝ (fun a => fun k => (w a k : ℝ)) ∧
          ∀ a, (fun k => (w a k : ℝ)) ∈ t • K}) ∧
      (∀ (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓN : ℓ ≤ N) (y : Fin N → ℤ),
        gauge K (fun k => (y k : ℝ)) <
          sInf {t : ℝ | 0 < t ∧ ∃ w : Fin ℓ → (Fin N → ℤ),
            LinearIndependent ℝ (fun a => fun k => (w a k : ℝ)) ∧
            ∀ a, (fun k => (w a k : ℝ)) ∈ t • K} →
        (fun k => (y k : ℝ)) ∈
          Submodule.span ℝ (Set.range (fun j : Fin (ℓ - 1) =>
            (fun k => (v (Fin.castLE (by omega) j) k : ℝ))))) := by
  classical
  obtain ⟨x₀, hx₀int⟩ := hint
  have h0int : (0 : Fin N → ℝ) ∈ interior K := by
    have h := hconv.combo_interior_self_mem_interior hx₀int (hsym x₀ (interior_subset hx₀int))
      (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    simpa using h
  have h0K : (0 : Fin N → ℝ) ∈ K := interior_subset h0int
  have habs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0int)
  let S : ℕ → Set ℝ := fun ℓ => {t : ℝ | 0 < t ∧ ∃ w : Fin ℓ → (Fin N → ℤ),
      LinearIndependent ℝ (fun a => fun k => (w a k : ℝ)) ∧
      ∀ a, (fun k => (w a k : ℝ)) ∈ t • K}
  let lam : ℕ → ℝ := fun ℓ => sInf (S ℓ)
  have hS_bdd : ∀ ℓ, BddBelow (S ℓ) := fun ℓ => ⟨0, fun t ht => ht.1.le⟩
  have hS_ne : ∀ ℓ, ℓ ≤ N → (S ℓ).Nonempty := by
    intro ℓ hℓN
    rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓpos
    · subst hℓ0
      refine ⟨1, by norm_num, (fun a : Fin 0 => Fin.elim0 a), ?_, fun a => Fin.elim0 a⟩
      rw [Fintype.linearIndependent_iff]
      intro g _ j
      exact Fin.elim0 j
    · let w : Fin ℓ → (Fin N → ℤ) := fun a => Pi.single (Fin.castLE hℓN a) (1:ℤ)
      have key : (fun a : Fin ℓ => fun k => (w a k : ℝ)) =
          fun a : Fin ℓ => (Pi.basisFun ℝ (Fin N)) (Fin.castLE hℓN a) := by
        funext a k
        rw [Pi.basisFun_apply]
        change ((w a) k : ℝ) = ((Pi.single (Fin.castLE hℓN a) (1:ℝ) : Fin N → ℝ)) k
        rw [show w a = Pi.single (Fin.castLE hℓN a) (1:ℤ) from rfl]
        by_cases hk : k = Fin.castLE hℓN a
        · subst hk; simp
        · rw [Pi.single_eq_of_ne (h := hk), Pi.single_eq_of_ne (h := hk)]
          simp
      have hwLI : LinearIndependent ℝ (fun a : Fin ℓ => fun k => (w a k : ℝ)) := by
        rw [key]
        exact (Pi.basisFun ℝ (Fin N)).linearIndependent.comp (Fin.castLE hℓN)
          (Fin.castLE_injective hℓN)
      haveI : Nonempty (Fin ℓ) := ⟨⟨0, hℓpos⟩⟩
      let r : Fin ℓ → ℝ := fun a =>
        Classical.choose (habs.gauge_set_nonempty (x := (fun k => (w a k : ℝ))))
      have hr : ∀ a : Fin ℓ, 0 < r a ∧ (fun k => (w a k : ℝ)) ∈ r a • K := fun a =>
        Classical.choose_spec (habs.gauge_set_nonempty (x := (fun k => (w a k : ℝ))))
      let t : ℝ := Finset.univ.sup' Finset.univ_nonempty r
      have htpos : 0 < t := lt_of_lt_of_le (hr ⟨0, hℓpos⟩).1
        (Finset.le_sup' r (Finset.mem_univ _))
      refine ⟨t, htpos, w, hwLI, fun a => ?_⟩
      exact smul_subset_smul_of_le_of_mem_zero hconv h0K (hr a).1.le
        (Finset.le_sup' r (Finset.mem_univ a)) (hr a).2
  have hmono : ∀ {i j : ℕ}, i ≤ j → j ≤ N → lam i ≤ lam j := by
    intro i j hij hjN
    have hsub : S j ⊆ S i := by
      intro t ht
      obtain ⟨ht0, w, hwLI, hwm⟩ := ht
      exact ⟨ht0, (fun a : Fin i => w (Fin.castLE hij a)),
        hwLI.comp (Fin.castLE hij) (Fin.castLE_injective hij),
        fun a => hwm (Fin.castLE hij a)⟩
    exact le_csInf (hS_ne j hjN) (fun s hs => csInf_le (hS_bdd i) (hsub hs))
  -- Step A: recursive construction of the realising family
  let P : ℕ → Prop := fun i => i ≤ N → ∃ v : Fin i → (Fin N → ℤ),
      LinearIndependent ℝ (fun j => fun k => (v j k : ℝ)) ∧
      ∀ j : Fin i, gauge K (fun k => (v j k : ℝ)) ≤ lam (j.val + 1)
  have hP0 : P 0 := by
    intro _
    refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g _ j
      exact absurd j.isLt (Nat.not_lt_zero j.val)
    · intro j
      exact absurd j.isLt (Nat.not_lt_zero j.val)
  have hstep : ∀ i, P i → P (i+1) := by
    intro i hPi hi1
    have hiN : i ≤ N := Nat.le_of_succ_le hi1
    obtain ⟨v, hvLI, hvb⟩ := hPi hiN
    let W : Submodule ℝ (Fin N → ℝ) :=
      Submodule.span ℝ (Set.range (fun j : Fin i => (fun k => (v j k : ℝ))))
    have hWfin : Module.finrank ℝ W = i := by
      have h := finrank_span_eq_card (R := ℝ) hvLI
      simpa [W] using h
    have hWN : W ≠ ⊤ := by
      intro hWtop
      have h1 : Module.finrank ℝ W = Module.finrank ℝ (Fin N → ℝ) := by
        rw [hWtop]
        exact finrank_top ℝ (Fin N → ℝ)
      rw [hWfin, Module.finrank_fin_fun] at h1
      omega
    obtain ⟨z0, hz0⟩ := exists_int_vector_notMem hWN
    let Tset : Set (Fin N → ℤ) := {z : Fin N → ℤ | (fun k => (z k : ℝ)) ∉ W ∧
        gauge K (fun k => (z k : ℝ)) ≤ gauge K (fun k => (z0 k : ℝ))}
    have hTfin : Tset.Finite :=
      (finite_int_points_gauge_le_local hconv h0int hbdd _).subset (fun z hz => hz.2)
    have hTne : hTfin.toFinset.Nonempty :=
      ⟨z0, by rw [Set.Finite.mem_toFinset]; exact ⟨hz0, le_rfl⟩⟩
    obtain ⟨x, hxT, hxmin⟩ := Finset.exists_min_image hTfin.toFinset
      (fun z => gauge K (fun k => (z k : ℝ))) hTne
    have hxTset : x ∈ Tset := (Set.Finite.mem_toFinset hTfin).mp hxT
    have hxmin' : ∀ z ∈ Tset, gauge K (fun k => (x k : ℝ)) ≤ gauge K (fun k => (z k : ℝ)) :=
      fun z hz => hxmin z ((Set.Finite.mem_toFinset hTfin).mpr hz)
    have hxW : (fun k => (x k : ℝ)) ∉ W := hxTset.1
    have hxbound : gauge K (fun k => (x k : ℝ)) ≤ lam (i+1) := by
      by_contra hnot
      rw [not_le] at hnot
      obtain ⟨t, htS, htlt⟩ := (csInf_lt_iff (hS_bdd (i+1)) (hS_ne (i+1) hi1)).mp hnot
      obtain ⟨ht0, w, hwLI, hwm⟩ := htS
      have hw_out : ∃ a : Fin (i+1), (fun k => (w a k : ℝ)) ∉ W := by
        by_contra h
        push Not at h
        have hle : Submodule.span ℝ
            (Set.range (fun a : Fin (i+1) => (fun k => (w a k : ℝ)))) ≤ W :=
          Submodule.span_le.mpr (fun x hx => by
            rcases hx with ⟨a, rfl⟩
            exact h a)
        have h1 : Module.finrank ℝ
            (Submodule.span ℝ (Set.range (fun a : Fin (i+1) => (fun k => (w a k : ℝ))))) = i + 1 := by
          have h := finrank_span_eq_card (R := ℝ) hwLI
          simpa using h
        have h2 := Submodule.finrank_mono hle
        rw [h1, hWfin] at h2
        omega
      obtain ⟨a, ha⟩ := hw_out
      have hga : gauge K (fun k => (w a k : ℝ)) ≤ t := gauge_le_of_mem ht0.le (hwm a)
      have hxa : gauge K (fun k => (x k : ℝ)) ≤ gauge K (fun k => (w a k : ℝ)) :=
        hxmin' (w a) ⟨ha, le_trans (le_trans hga htlt.le) hxTset.2⟩
      linarith
    let v' : Fin (i+1) → (Fin N → ℤ) := Fin.snoc v x
    have hv'_cast : ∀ k : Fin i, v' k.castSucc = v k := fun k => by
      change Fin.snoc (α := fun _ : Fin (i+1) => (Fin N → ℤ)) v x k.castSucc = v k
      exact Fin.snoc_castSucc (α := fun _ : Fin (i+1) => (Fin N → ℤ)) x v k
    have hv'_last : v' (Fin.last i) = x := by
      change Fin.snoc (α := fun _ : Fin (i+1) => (Fin N → ℤ)) v x (Fin.last i) = x
      exact Fin.snoc_last (α := fun _ : Fin (i+1) => (Fin N → ℤ)) x v
    refine ⟨v', ?_, ?_⟩
    · have hE : (fun j : Fin (i+1) => (fun k => (v' j k : ℝ))) =
          Fin.snoc (fun j : Fin i => (fun k => (v j k : ℝ))) (fun k => (x k : ℝ)) := by
        funext j
        cases j using Fin.lastCases with
        | last =>
            rw [hv'_last]
            exact (Fin.snoc_last (α := fun _ : Fin (i+1) => (Fin N → ℝ))
              (x := (fun k : Fin N => (x k : ℝ)))
              (p := fun j : Fin i => fun k => (v j k : ℝ))).symm
        | cast j =>
            rw [hv'_cast j]
            exact (Fin.snoc_castSucc (α := fun _ : Fin (i+1) => (Fin N → ℝ))
              (x := (fun k : Fin N => (x k : ℝ)))
              (p := fun j : Fin i => fun k => (v j k : ℝ)) j).symm
      rw [hE]
      exact (linearIndependent_finSnoc (K := ℝ) (x := fun k => (x k : ℝ))
        (v := fun j : Fin i => fun k => (v j k : ℝ))).2 ⟨hvLI, hxW⟩
    · intro j
      by_cases hji : j.val = i
      · have hjl : j = Fin.last i := Fin.ext hji
        rw [hjl, hv'_last]
        exact hxbound
      · have hjlt : j.val < i := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) (fun h => hji h)
        let k : Fin i := ⟨j.val, hjlt⟩
        have hk : j = k.castSucc := Fin.ext rfl
        rw [hk, hv'_cast k]
        exact hvb k
  have hPN : P N := Nat.rec hP0 hstep N
  obtain ⟨v, hvLI, hvb⟩ := hPN le_rfl
  refine ⟨v, hvLI, hvb, ?_⟩
  -- Step B: interior exclusion
  let T : ℕ → Set (Fin N → ℝ) := fun n => {x : Fin N → ℝ |
      ∃ j : Fin N, j.val < n - 1 ∧ x = (fun k => (v j k : ℝ))}
  have hT_eq : ∀ (n : ℕ) (hn : n ≤ N),
      T (n+1) = Set.range (fun j : Fin n => (fun k => (v (Fin.castLE hn j) k : ℝ))) := by
    intro n hn
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨⟨j.val, hj⟩, ?_⟩
      exact congrArg (fun z : Fin N => (fun k => (v z k : ℝ))) (Fin.ext rfl)
    · rintro ⟨j, rfl⟩
      exact ⟨Fin.castLE hn j, j.isLt, rfl⟩
  have hmain : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ N → ∀ y : Fin N → ℤ,
      gauge K (fun k => (y k : ℝ)) < lam ℓ →
      (fun k => (y k : ℝ)) ∈ Submodule.span ℝ (T ℓ) := by
    intro ℓ
    induction ℓ with
    | zero => intro h1; omega
    | succ ℓ ih =>
      intro h1 hn y hy
      rcases Nat.eq_zero_or_pos ℓ with hℓ0 | hℓ1
      · subst hℓ0
        have hy0 : (fun k => (y k : ℝ)) = 0 := by
          by_contra hne
          have hLI1 : LinearIndependent ℝ (fun _ : Fin 1 => (fun k => (y k : ℝ))) :=
            linearIndependent_unique_iff.mpr hne
          have hmid : gauge K (fun k => (y k : ℝ)) <
              (gauge K (fun k => (y k : ℝ)) + lam 1) / 2 := by linarith
          obtain ⟨b, hb0, hblt, hbmem⟩ := exists_lt_of_gauge_lt habs hmid
          have hbS : b ∈ S 1 := ⟨hb0, (fun _ : Fin 1 => y), hLI1, fun _ => hbmem⟩
          have := csInf_le (hS_bdd 1) hbS
          linarith
        rw [hy0]
        exact Submodule.zero_mem _
      · have hℓN : ℓ ≤ N := by omega
        have hmonoℓ : lam ℓ ≤ lam (ℓ+1) := hmono (Nat.le_succ ℓ) hn
        by_cases hEq : lam ℓ = lam (ℓ+1)
        · have hy' : gauge K (fun k => (y k : ℝ)) < lam ℓ := by rw [← hEq] at hy; exact hy
          have hmem := ih hℓ1 hℓN y hy'
          refine Submodule.span_mono ?_ hmem
          rintro x ⟨j, hj, rfl⟩
          exact ⟨j, by omega, rfl⟩
        · have hgap : lam ℓ < lam (ℓ+1) := lt_of_le_of_ne hmonoℓ hEq
          by_contra hmem
          have hnotR : (fun k => (y k : ℝ)) ∉ Submodule.span ℝ
              (Set.range (fun j : Fin ℓ => (fun k => (v (Fin.castLE hℓN j) k : ℝ)))) := by
            intro hR
            exact hmem (by rw [hT_eq ℓ hℓN]; exact hR)
          have hLIu : LinearIndependent ℝ
              (fun j : Fin ℓ => (fun k => (v (Fin.castLE hℓN j) k : ℝ))) :=
            hvLI.comp (Fin.castLE hℓN) (Fin.castLE_injective hℓN)
          let fE : Fin (ℓ+1) → (Fin N → ℝ) :=
            Fin.snoc (fun j : Fin ℓ => (fun k => (v (Fin.castLE hℓN j) k : ℝ)))
              (fun k => (y k : ℝ))
          have hfE : LinearIndependent ℝ fE :=
            (linearIndependent_finSnoc (K := ℝ) (x := (fun k => (y k : ℝ)))
              (v := fun j : Fin ℓ => (fun k => (v (Fin.castLE hℓN j) k : ℝ)))).2
              ⟨hLIu, hnotR⟩
          let f : Fin (ℓ+1) → (Fin N → ℤ) :=
            Fin.snoc (fun j : Fin ℓ => v (Fin.castLE hℓN j)) y
          have hf_img : (fun a : Fin (ℓ+1) => (fun k => (f a k : ℝ))) = fE := by
            funext a
            cases a using Fin.lastCases with
            | last => simp [f, fE]
            | cast j => simp [f, fE]
          have hfLI : LinearIndependent ℝ (fun a : Fin (ℓ+1) => fun k => (f a k : ℝ)) := by
            rw [hf_img]
            exact hfE
          have hf_last : f (Fin.last ℓ) = y := by
            change Fin.snoc (α := fun _ : Fin (ℓ+1) => (Fin N → ℤ))
              (fun j : Fin ℓ => v (Fin.castLE hℓN j)) y (Fin.last ℓ) = y
            exact Fin.snoc_last (α := fun _ : Fin (ℓ+1) => (Fin N → ℤ)) y _
          have hf_cast : ∀ j : Fin ℓ, f j.castSucc = v (Fin.castLE hℓN j) := fun j => by
            change Fin.snoc (α := fun _ : Fin (ℓ+1) => (Fin N → ℤ))
              (fun j : Fin ℓ => v (Fin.castLE hℓN j)) y j.castSucc = v (Fin.castLE hℓN j)
            exact Fin.snoc_castSucc (α := fun _ : Fin (ℓ+1) => (Fin N → ℤ)) y _ j
          have hf_lt : ∀ a : Fin (ℓ+1), gauge K (fun k => (f a k : ℝ)) < lam (ℓ+1) := by
            intro a
            by_cases ha : a.val = ℓ
            · have haj : a = Fin.last ℓ := Fin.ext ha
              rw [haj, hf_last]
              exact hy
            · have halt : a.val < ℓ := lt_of_le_of_ne (Nat.lt_succ_iff.mp a.isLt) (fun h => ha h)
              let j : Fin ℓ := ⟨a.val, halt⟩
              have haj : a = j.castSucc := Fin.ext rfl
              rw [haj, hf_cast j]
              have h2 : gauge K (fun k => (v (Fin.castLE hℓN j) k : ℝ)) ≤ lam (j.val + 1) :=
                hvb (Fin.castLE hℓN j)
              have h3 : lam (j.val + 1) ≤ lam ℓ := hmono (by omega) hℓN
              linarith
          choose b' hb' using fun a : Fin (ℓ+1) => exists_lt_of_gauge_lt habs (hf_lt a)
          haveI : Nonempty (Fin (ℓ+1)) := ⟨⟨0, by omega⟩⟩
          let b : ℝ := Finset.univ.sup' Finset.univ_nonempty b'
          have hbpos : 0 < b := lt_of_lt_of_le (hb' ⟨0, by omega⟩).1
            (Finset.le_sup' b' (Finset.mem_univ _))
          have hblt : b < lam (ℓ+1) :=
            (Finset.sup'_lt_iff Finset.univ_nonempty (f := b')).2 (fun a _ => (hb' a).2.1)
          have hbS : b ∈ S (ℓ+1) := ⟨hbpos, f, hfLI, fun a =>
            smul_subset_smul_of_le_of_mem_zero hconv h0K (hb' a).1.le
              (Finset.le_sup' b' (Finset.mem_univ a)) (hb' a).2.2⟩
          have := csInf_le (hS_bdd (ℓ+1)) hbS
          linarith
  intro ℓ hℓ1 hℓN y hy
  have hmem : (fun k => (y k : ℝ)) ∈ Submodule.span ℝ (T ℓ) := hmain ℓ hℓ1 hℓN y hy
  refine Submodule.span_mono ?_ hmem
  rintro x ⟨j, hj, rfl⟩
  refine ⟨⟨j.val, hj⟩, ?_⟩
  exact congrArg (fun z : Fin N => (fun k => (v z k : ℝ))) (Fin.ext rfl)

end Commons.GeometryOfNumbers.SuccessiveMinima
